module Dhall.TypeCheck.State where

import Prelude

import Control.Comonad (extract)
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NEA
import Data.FoldableWithIndex (foldMapWithIndex)
import Data.Functor.Variant as VariantF
import Data.Maybe (Maybe(..), fromJust, maybe')
import Data.Newtype (unwrap, wrap)
import Data.Semigroup.Foldable (foldMap1)
import Data.These (These(..))
import Data.Traversable (sequence)
import Data.Tuple (Tuple(..))
import Data.Variant (Variant)
import Data.Variant as Variant
import Dhall.Core (Expr, Pair(..), S_, _S, alphaNormalize)
import Dhall.Core.AST as AST
import Dhall.Core.AST.Operations.Transformations (GenericExprAlgebra, NodeOps, runAlgebraExpr, runOverCases)
import Dhall.Core.Zippers.Merge (mergeWith)
import Dhall.Lib.MonoidalState (class ErrorMonoid, Discrete(..), ErrorPart, Inconsistency, LocStateErroring(..), StateErroring(..), StatePart, Total(..), mkStatePart, unErrorPart, unStatePart)
import Dhall.Map (class MapLike)
import Dhall.TypeCheck.Operations (normalizeStep, plain, topLoc)
import Dhall.TypeCheck.Types (LFeedback, Oxpr, TCState, L)
import Dhall.TypeCheck.Universes as U
import Partial.Unsafe (unsafePartial)
import Unsafe.Reference (unsafeRefEq)

type StateErrors r =
  ( "Unification error" ::
    { key :: U.SolverKey
    , value :: Inconsistency U.SolverVal
    }
  | r
  )

liftErrors :: forall w m a r. Monoid w => ErrorPart (Tuple (Total w) (TCState (L m a))) -> NonEmptyArray (Tuple (L m a) (Variant (StateErrors r)))
liftErrors = unErrorPart >>> unThese >>> foldMapWithIndex liftError >>> NEA.fromArray >>> unsafePartial fromJust
  where
    unThese (This e) = absurd e
    unThese (Both e _) = absurd e
    unThese (That e) = e

    liftError k i = pure $ Tuple (loc i) (Variant.inj (_S::S_ "Unification error") { key: k, value: strip i })

    strip = map \(Tuple _ (Discrete v)) -> v
    loc = foldMap1 \(Tuple (Total l) _) -> NEA.head l

tcState :: forall to tm tw m a. ErrorMonoid to tm tw => StatePart (Tuple tw (TCState (L m a))) -> StatePart (TCState (L m a))
tcState = mkStatePart <<< extract <<< unStatePart

substitute :: forall l m a node ops.
  GenericExprAlgebra (NodeOps (AST.ExprLayerRow m a) (StatePart (TCState l)) node ops) (StatePart (TCState l)) node
substitute us alg = pure <<< runOverCases alg.overlayer (unwrap <<< alg.recurse us)
  { "Const": unwrap >>> U.substitute (unStatePart us) >>> wrap }

substituteExpr :: forall l m a. StatePart (TCState l) -> Expr m a -> Expr m a
substituteExpr = runAlgebraExpr substitute

unify :: forall w r m a. Eq a => MapLike String m =>
  (Unit -> LFeedback w r m a Void) ->
  (Pair AST.Const -> LFeedback w r m a Void) ->
  Oxpr w r m a -> Oxpr w r m a ->
  LFeedback w r m a Unit
unify _ _ ty0 ty1 | unsafeRefEq ty0 ty1 = pure unit -- perhaps there is enough sharing
unify uniError constError ty0 ty1 =
  let
    Pair ty0' ty1' = Pair ty0 ty1 <#>
      -- it appears that alphaNormalize is cheaper after `plain`,
      -- even though it is shared in `Oxpr`
      normalizeStep >>> plain >>> AST.unordered >>> alphaNormalize
    unifyAll a b = AST.embedW <$> unifyLayer (AST.projectW a) (AST.projectW b)
    unifyLayer l r = ((#) r) $ ((#) l) $ VariantF.on (_S::S_ "Const")
      do
        \a ->
          VariantF.on (_S::S_ "Const")
            do \b -> unifyConst (unwrap a) (unwrap b) <#> VariantF.inj (_S::S_ "Const") <<< wrap
            do \_ -> absurd <$> uniError unit
      do
        \_ ->
          VariantF.on (_S::S_ "Const")
            do \_ -> absurd <$> uniError unit
            do \_ -> maybe' (map absurd <<< uniError) sequence (mergeWith unifyAll l r)
    unifyConst a b | Just (Tuple w c) <- U.unifyConst (topLoc ty0) a (topLoc ty1) b =
      LocStateErroring \_ -> Success (mkStatePart (Tuple mempty w)) c
    unifyConst a b = absurd <$> constError (Pair a b)
  in void $ unifyAll ty0' ty1'

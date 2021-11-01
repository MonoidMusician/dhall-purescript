module Dhall.TypeCheck ( module Dhall.TypeCheck, module Exports ) where

import Prelude

import Control.Comonad (extend)
import Control.Plus (empty)
import Data.Bifunctor (bimap)
import Data.Foldable (foldr, oneOfMap)
import Data.Lens (preview)
import Data.List.Types (NonEmptyList(..))
import Data.Maybe (Maybe(..))
import Data.Newtype (un)
import Data.NonEmpty ((:|))
import Data.These (These(..), theseLeft)
import Data.Tuple (Tuple(..))
import Data.Variant (Variant)
import Data.Variant as Variant
import Dhall.Context (Context)
import Dhall.Context as Dhall.Context
import Dhall.Core (Var(..), alphaNormalize)
import Dhall.Core as Variables
import Dhall.Core.AST (Expr, ExprRowVF(..), ExprRowVFI, S_, _S)
import Dhall.Core.AST.Operations.Location (Derivation, Derived, Operated, Within)
import Dhall.Core.AST.Operations.Location as Loc
import Dhall.Core.Zippers (_ix)
import Dhall.Lib.MonoidalState as V
import Dhall.Map (class MapLike)
import Dhall.Normalize as Dhall.Normalize
import Dhall.TypeCheck.Errors (Reference(..), explain)
import Dhall.TypeCheck.Operations (alphaNormalizeStep, contextStep, normalizeStep, originateFrom, plain, reconstituteCtxM, shiftOxpr, substContextExpr0, substContextExprCtx, substContextOxprCtx, topLoc, typecheckSketch, typecheckStep, unlayerO)
import Dhall.TypeCheck.Rules (typecheckAlgebra)
import Dhall.TypeCheck.State as State
import Dhall.TypeCheck.Types (Ann, BiContext, Errors, Feedback, FeedbackE, Inconsistency(..), L, Lxpr, LxprF, Operations, Ospr, OsprE, Oxpr, OxprE, Result, ResultE, SubstContext, TypeCheckError, TypeCheckErrorE, WithBiCtx(..)) as Exports
import Dhall.TypeCheck.Types (BiContext, Errors, FeedbackE, L, OxprE, ResultE, TypeCheckError)
import Dhall.Variables (MaybeIntro(..), trackIntro)
import Matryoshka (project)
import Validation.These as VV

-- | Function that converts the value inside an `Embed` constructor into a new
-- | expression.
type Typer m a = a -> Expr m a

locateO' :: forall w r m a. Eq a => MapLike String m =>
  OxprE w ( "Not found" :: ExprRowVFI | r ) m a ->
  Variant (Operated (Derived (Within ()))) ->
  FeedbackE w ( "Not found" :: ExprRowVFI | r ) m a
    (OxprE w ( "Not found" :: ExprRowVFI | r ) m a)
locateO' foc0 = Variant.match
  { substitute: \{} -> pure $
      substContextOxprCtx (theseLeft <$> contextStep foc0) foc0
  , shift: \{ delta, variable } -> pure $
      shiftOxpr delta variable foc0
  , alphaNormalize: \{} -> pure $ alphaNormalizeStep foc0
  , normalize: \{} -> typecheckStep foc0 <#> \_ -> normalizeStep foc0
  , typecheck: \{} -> typecheckStep foc0
  , within: \i ->
      foc0 # unlayerO # ERVF # preview (_ix i) # do
        V.note $ Tuple (topLoc foc0) $ Variant.inj (_S::S_ "Not found") i
  }

locateO :: forall w r m a. Eq a => MapLike String m =>
  OxprE w ( "Not found" :: ExprRowVFI | r ) m a ->
  Derivation ->
  FeedbackE w ( "Not found" :: ExprRowVFI | r ) m a
    (OxprE w ( "Not found" :: ExprRowVFI | r ) m a)
locateO foc0 deriv = foldr (\v foc -> foc >>= flip locateO' v) (pure foc0) deriv

locateE' :: forall w r m a. Eq a => MapLike String m =>
  (a -> Expr m a) ->
  Variant (Operated (Derived (Within ()))) ->
  Tuple (BiContext (Expr m a)) (Expr m a) ->
  FeedbackE w ( "Not found" :: ExprRowVFI | r ) m a
    (Tuple (BiContext (Expr m a)) (Expr m a))
locateE' tpa = Variant.match
  let
    substCtx = extend \(Tuple ctx e) -> substContextExpr0 (theseLeft <$> ctx) e
    tc ctx0 e0 = map plain <<< typecheckStep =<< typingWithA tpa ctx0 e0
    typecheck (Tuple ctx e) = do
      ctx' <- ctx # reconstituteCtxM \ctx' -> case _ of
        This val -> tc ctx' val
        That ty -> pure ty
        Both _ ty -> pure ty
      Tuple ctx <$> tc ctx' e
  in
  { substitute: \{} -> \(Tuple ctx e) ->
      pure (Tuple ctx (substContextExprCtx (theseLeft <$> ctx) e))
  , alphaNormalize: \{} -> \(Tuple ctx e) ->
      pure $ Tuple ctx $ alphaNormalize e
  , normalize: \{} -> substCtx >>> \(Tuple ctx e) -> do
      -- Ensure it typechecks before substituting and normalizing
      -- TODO: safe normalization fallback?
      void $ typecheck (Tuple ctx e)
      pure $ Tuple ctx $ Dhall.Normalize.normalize e
  , shift: \i -> pure <<< map (Variables.shift i.delta i.variable)
  -- I guess we need to substitute `let`-bound variables in context
  -- before typechecking
  , typecheck: \{} -> substCtx >>> typecheck
  , within: \i -> \(Tuple ctx e) ->
      let
        intro = Tuple <<< case _ of
          DoNothing -> ctx
          Clear -> Dhall.Context.empty
          Intro (Tuple k th) -> join bimap (Variables.shift 1 (V k 0)) <$>
            Dhall.Context.insert k th ctx
      in e # project # un ERVF # trackIntro intro # ERVF # preview (_ix i) # do
        V.note $ Tuple (pure (Tuple empty empty)) $ Variant.inj (_S::S_ "Not found") i
  }

locateE :: forall w r m a. Eq a => MapLike String m =>
  (a -> Expr m a) ->
  Derivation ->
  { expr :: Expr m a, ctx :: BiContext (Expr m a) } ->
  FeedbackE w ( "Not found" :: ExprRowVFI | r ) m a
    { expr :: Expr m a, ctx :: BiContext (Expr m a) }
locateE tpa deriv { expr, ctx } =
  (foldr (\v c -> c >>= locateE' tpa v) (pure $ Tuple ctx expr) deriv) <#>
    \(Tuple ctx' expr') -> { expr: expr', ctx: ctx' }

-- | Type-check an expression and return the expression's type if type-checking
-- | succeeds or an error if type-checking fails
-- | `typeWith` does not necessarily normalize the type since full normalization
-- | is not necessary for just type-checking.  If you actually care about the
-- | returned type then you may want to `Dhall.Core.normalize` it afterwards.
-- | The supplied `Context` records the types of the names in scope. If
-- | these are ill-typed, the return value may be ill-typed.
typeWith :: forall r m.
  MapLike String m =>
  Context (Expr m Void) ->
  Expr m Void ->
  ResultE (State.StateErrors r) m Void (Expr m Void)
typeWith = typeWithA absurd

-- | `typeOf` is the same as `typeWith` with an empty context, meaning that the
-- | expression must be closed (i.e. no free variables), otherwise type-checking
-- | will fail.
typeOf :: forall r m.
  MapLike String m =>
  Expr m Void ->
  ResultE (State.StateErrors r) m Void (Expr m Void)
typeOf = typeWith Dhall.Context.empty

-- | Generalization of `typeWith` that allows type-checking the `Embed`
-- |  constructor with custom logic
typeWithA :: forall r m a.
  Eq a => MapLike String m =>
  Typer m a ->
  Context (Expr m a) ->
  Expr m a ->
  ResultE (State.StateErrors r) m a (Expr m a)
typeWithA tpa ctx0 e0 = case map plain <<< typecheckStep =<< typingWithA tpa ctx0 e0 of
  V.Success s a -> VV.Success (State.substituteExpr (State.tcState s) a)
  V.Error es s ma ->
    let
      es' = case es of
        That e -> e
        This o -> State.liftErrors o
        Both o e -> State.liftErrors o <> e
    in VV.Error es' (State.substituteExpr (State.tcState s) <$> ma)

typingWithA :: forall w r m a.
  Eq a => MapLike String m =>
  Typer m a ->
  Context (Expr m a) ->
  Expr m a ->
  FeedbackE w r m a (OxprE w r m a)
typingWithA tpa ctx0 e0 = do
  let
    tcingFrom foc = typecheckSketch (typecheckAlgebra (pure <<< tpa)) <<< originateFrom foc
    -- Convert an Expr to an Oxpr and typecheck in the given context
    -- (which must consist of Ospr)
    tcingIn :: BiContext (OxprE w r m a) -> Expr m a -> FeedbackE w r m a (OxprE w r m a)
    tcingIn ctx e =
      let
        e' = tcingFrom (pure (Tuple empty (Just e))) e ctx
      in e' <$ typecheckStep e'
  -- convert ctx0 and e0 to Ospr
  ctxO <- reconstituteCtxM (\ctx ty -> That <$> tcingIn ctx ty) ctx0
  let eO = tcingFrom (pure (Tuple empty Nothing)) e0
  -- and run typechecking on eO
  pure $ eO ctxO

oneStopShop ::
  forall w m a.
    MapLike String m => Eq a => Show a =>
  (a -> FeedbackE w ( "Not found" :: ExprRowVFI ) m a (Expr m a)) ->
  Expr m a ->
  { oxpr :: OxprE w ( "Not found" :: ExprRowVFI ) m a
  , locate :: L m a ->
      FeedbackE w ( "Not found" :: ExprRowVFI ) m a
        (OxprE w ( "Not found" :: ExprRowVFI ) m a)
  , explain ::
      TypeCheckError (Errors ( "Not found" :: ExprRowVFI )) (L m a) ->
      Array (Reference (Maybe (OxprE w ( "Not found" :: ExprRowVFI ) m a)))
  }
oneStopShop tpa e0 = { oxpr, locate, explain: explainHere } where
  oxprFrom loc ei =
    (#) Dhall.Context.empty $
      typecheckSketch (typecheckAlgebra tpa) $
        originateFrom (pure (Tuple empty loc)) $
          ei
  oxpr = oxprFrom Nothing e0
  get (Tuple loc me) = flip locateO loc $ case me of
    Nothing -> oxpr
    Just e1 -> oxprFrom (Just e1) e1
  locate (NonEmptyList (a :| as)) =
    case get a of
      suc@(V.Success _ _) -> suc
      err@(V.Error _ _ _) ->
        case oneOfMap (V.hush' <<< get) as of
          Nothing -> err
          Just r -> pure r
  explainNotFound :: forall b. String -> Array (Reference b)
  explainNotFound i =
    [ Text $ "Could not find location: " <> i ]
  explainHere (Tuple location tag0) =
    tag0 # Variant.on (_S::S_ "Not found" ) (explainNotFound <<< show) \tag ->
      let
        located = V.hush' $ locate location
        addLocation :: Loc.BasedExprDerivation m a -> L m a
        addLocation (Tuple path (Just base)) = pure $ Tuple path (Just base)
        addLocation (Tuple path Nothing) = bimap (path <> _) identity <$> location
      in case located of
        Just el ->
          let
            ctx = join bimap (const unit) <$> contextStep el
            nodeType = unit <$ unlayerO el
          in explain ctx nodeType tag <#> map (V.hush' <<< locate <<< addLocation)
        Nothing -> explainNotFound (show location)

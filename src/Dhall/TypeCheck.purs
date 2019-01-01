module Dhall.TypeCheck where

import Prelude

import Control.Alternative (class Alternative)
import Control.Comonad (class Comonad, extract)
import Control.Comonad.Cofree (Cofree, buildCofree, hoistCofree)
import Control.Comonad.Cofree as Cofree
import Control.Comonad.Env (EnvT(..), mapEnvT, runEnvT)
import Control.Monad.Reader (ReaderT(..), runReaderT)
import Control.Monad.Writer (WriterT)
import Control.Plus (empty)
import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Bifoldable (bifoldMap, bifoldl, bifoldr)
import Data.Bifunctor (bimap)
import Data.Bitraversable (bisequence, bitraverse)
import Data.Const as Const
import Data.Either (Either(..))
import Data.Foldable (class Foldable, foldMap, foldr, foldl, for_, traverse_)
import Data.FoldableWithIndex (class FoldableWithIndex, foldMapWithIndex, forWithIndex_)
import Data.Function (on)
import Data.Functor.App (App(..))
import Data.Functor.Compose (Compose(..))
import Data.Functor.Mu (Mu(..))
import Data.Functor.Product (Product(..))
import Data.Functor.Variant (FProxy, SProxy)
import Data.Functor.Variant as VariantF
import Data.FunctorWithIndex (class FunctorWithIndex, mapWithIndex)
import Data.Identity (Identity(..))
import Data.Lazy (Lazy, defer)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.List (List(..), (:))
import Data.List as List
import Data.List.NonEmpty as NEL
import Data.List.Types (NonEmptyList)
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Maybe.First (First(..))
import Data.Monoid.Disj (Disj(..))
import Data.Natural (Natural)
import Data.Newtype (class Newtype, over, un, unwrap, wrap)
import Data.Newtype as N
import Data.NonEmpty (NonEmpty, (:|))
import Data.Profunctor.Strong ((&&&))
import Data.Semigroup.Foldable (class Foldable1)
import Data.Set (Set)
import Data.Set as Set
import Data.Symbol (class IsSymbol)
import Data.These (These(..), theseLeft)
import Data.Traversable (class Traversable, for, sequence, traverse)
import Data.TraversableWithIndex (class TraversableWithIndex, forWithIndex)
import Data.Tuple (Tuple(..), curry, uncurry)
import Data.Variant (Variant)
import Data.Variant as Variant
import Dhall.Context (Context(..))
import Dhall.Context as Dhall.Context
import Dhall.Core (Var, shift)
import Dhall.Core as Dhall.Core
import Dhall.Core.AST (Const(..), Expr, ExprRowVF(..), Pair(..), S_, _S)
import Dhall.Core.AST as AST
import Dhall.Core.AST.Operations.Location (BasedExprDerivation, ExprLocation)
import Dhall.Core.AST.Operations.Location as Loc
import Dhall.Core.AST.Operations.Transformations (OverCases, OverCasesM(..))
import Dhall.Core.StrMapIsh (class StrMapIsh)
import Dhall.Core.StrMapIsh as StrMapIsh
import Dhall.Normalize as Dhall.Normalize
import Dhall.Variables (freeInAlg, shiftAlgG, trackIntro)
import Matryoshka (class Corecursive, class Recursive, ana, cata, embed, mapR, project, transCata, traverseR)
import Type.Row as R
import Validation.These as V

axiom :: forall f. Alternative f => Const -> f Const
axiom Type = pure Kind
axiom Kind = empty
-- axiom Kind = pure Sort
-- axiom Sort = Left (TypeError Dhall.Context.empty (Const Sort) Untyped)

rule :: forall f. Alternative f => Const -> Const -> f Const
rule Type Type = pure Type
rule Kind Type = pure Type
rule Kind Kind = pure Kind
{-
rule Sort Type = pure Type
rule Sort Kind = pure Kind
rule Sort Sort = pure Sort
-}
-- This forbids dependent types. If this ever changes, then the fast
-- path in the Let case of typeWithA will become unsound.
rule _    _    = empty

{-| Function that converts the value inside an `Embed` constructor into a new
    expression
-}
type Typer m a = a -> Expr m a

suggest :: forall w r m a x y. x -> Feedback w r m a y -> Feedback w r m a x
suggest a = (<<<) wrap $ unwrap >>> case _ of
  V.Success (Tuple _ accum) ->
    V.Success (Tuple a accum)
  V.Error es mtaccum ->
    V.Error es $ pure $ Tuple a $ foldMap extract mtaccum

newtype TypeCheckError r f = TypeCheckError
  -- The main location where the typechecking error occurred
  { location :: f
  -- The tag for the specific error, mostly for machine purposes
  , tag :: Variant r
  }
derive instance functorTypeCheckError :: Functor (TypeCheckError r)

type WR w e = WriterT (Array (Variant w)) (V.Erroring e)
type Feedback w r m a = WR w (TypeCheckError r (L m a))

-- I don't know how to explain this. I think it makes sense.
type TwoD m f = Mu (Compose (Cofree m) f)

recursor2D ::
  forall t f m r.
    Recursive t f =>
    Corecursive r (Compose (Cofree m) f) =>
    Functor f =>
    Functor m =>
  (f r -> m t) -> t -> r
recursor2D f = go where
  go :: t -> r
  go = ana $ (<<<) Compose $ buildCofree $ (>>>) project $ do
    identity &&& \ft -> ft <#> go # f

head2D ::
  forall t f w r. Comonad w =>
    Recursive r (Compose w f) =>
    Corecursive t f =>
  r -> t
head2D = transCata $ extract <<< un Compose

step2D ::
  forall f m r. Functor m =>
    Recursive r (Compose (Cofree m) f) =>
    Corecursive r (Compose (Cofree m) f) =>
  r -> m r
step2D = project >>> un Compose >>> Cofree.tail >>> map (Compose >>> embed)

dubstep2D ::
  forall f m r. Bind m =>
    Recursive r (Compose (Cofree m) f) =>
    Corecursive r (Compose (Cofree m) f) =>
  r -> m r
dubstep2D = step2D <=< step2D

headAndSpine ::
  forall t a f.
    Corecursive t f =>
  Cofree f a -> Tuple a t
headAndSpine = Cofree.head &&& transCata (runEnvT >>> extract)

unEnvT :: forall e f a. EnvT e f a -> f a
unEnvT (EnvT (Tuple _ fa)) = fa

env :: forall e f a. EnvT e f a -> e
env (EnvT (Tuple e _)) = e

mapEnv :: forall e e' f a. (e -> e') -> EnvT e f a -> EnvT e' f a
mapEnv f (EnvT (Tuple e fa)) = EnvT (Tuple (f e) fa)

bitransProduct :: forall f g a h l b. (f a -> h b) -> (g a -> l b) -> Product f g a -> Product h l b
bitransProduct natF natG (Product e) = Product (bimap natF natG e)

type Ann m a = Cofree (AST.ExprRowVF m a)
-- Expressions end up being associated with many locations, trust me on this ...
type L m a = NonEmptyList (BasedExprDerivation m a)
-- Expr with Location for each node
type Lxpr m a = Ann m a (L m a)
-- Pattern Functor for Lxpr
type LxprF m a = EnvT (L m a) (AST.ExprRowVF m a)

-- Context of which variables have been introduced with their
-- types and/or values:
-- - `This`: `Let` binding with only a value and no type annotation
-- - `Both`: `Let` binding with a value and its type annotation
-- - `That`: `Lam`/`Pi` binding
type BiContext a = Context (These a a)
-- Context that only records which variables have concrete values in scope.
type SubstContext a = Context (Maybe a)
-- Product (Compose Context (Join These)) f, but without the newtypes
data WithBiCtx f a = WithBiCtx (BiContext a) (f a)
getBiCtx :: forall f a. WithBiCtx f a -> BiContext a
getBiCtx (WithBiCtx ctx _) = ctx
dropBiCtx :: forall f a. WithBiCtx f a -> f a
dropBiCtx (WithBiCtx _ fa) = fa
overBiCtx :: forall f g a. (f a -> g a) -> WithBiCtx f a -> WithBiCtx g a
overBiCtx fg (WithBiCtx ctx fa) = WithBiCtx ctx (fg fa)
instance functorWithBiCtx :: Functor f => Functor (WithBiCtx f) where
  map f (WithBiCtx ctx fa) = WithBiCtx (join bimap f <$> ctx) (f <$> fa)
instance foldableWithBiCtx :: Foldable f => Foldable (WithBiCtx f) where
  foldMap f (WithBiCtx ctx fa) = foldMap (join bifoldMap f) ctx <> foldMap f fa
  foldr f c (WithBiCtx ctx fa) = foldr (flip $ join bifoldr f) (foldr f c fa) ctx
  foldl f c (WithBiCtx ctx fa) = foldl f (foldl (join bifoldl f) c ctx) fa
instance traversableWithBiCtx :: Traversable f => Traversable (WithBiCtx f) where
  traverse f (WithBiCtx ctx fa) = WithBiCtx <$> traverse (join bitraverse f) ctx <*> traverse f fa
  sequence (WithBiCtx ctx fa) = WithBiCtx <$> traverse bisequence ctx <*> sequence fa

-- Operations that can be performed on AST nodes:
--   Left (Lazy): substitution+normalization (idempotent, but this isn't enforced ...)
--   Right (Lazy Feedback): typechecking
-- TODO: more operations? extensibility? connect to GenericExprAlgebra?
type Operations w r m a = Product Lazy (Compose Lazy (Feedback w r m a))
-- Operations, but requiring a context
-- NOTE: the expression type is fixed to Oxpr here. It seems to work.
type Operacions w r m a = ReaderT (BiContext (Oxpr w r m a)) (Operations w r m a)
-- Expr with Location, along the dual axes of Operations and the AST
type Oxpr w r m a = TwoD (Operations w r m a) (LxprF m a)
-- Oxpr, but where the operations still need the context
type Ocpr w r m a = TwoD (Operacions w r m a) (LxprF m a)

-- Transforms the simple "typecheck one thing" algorithm to the full-blown
-- Lxpr -> Ocpr transformation (which includes typechecking and normalizing
-- each node).
typecheckSketch :: forall w r m a. Eq a => StrMapIsh m =>
  (WithBiCtx (LxprF m a) (Oxpr w r m a) -> Feedback w r m a (Lxpr m a)) ->
  Lxpr m a -> Ocpr w r m a
typecheckSketch alg = recursor2D
  \layer@(EnvT (Tuple loc e)) -> ReaderT \ctx -> Product $ Tuple
      do defer \_ ->
          let ctx' = ctx <#> theseLeft >>> map head2D in
          normalizeLxpr $
          substContextLxpr ctx' $
          embed $ EnvT $ Tuple loc $ head2D <$> e
      do Compose $ defer \_ ->
          map (alsoOriginateFrom (Loc.step (_S::S_ "typecheck") <$> loc)) $
          alg $ WithBiCtx ctx $ (((layer))) #
            -- contextualize each child of `layer` in the proper context,
            -- adapted for its place in the AST
            -- (in particular, if `layer` is `Let`/`Pi`/`Lam`)
            do mapEnvT $ _Newtype $ bicontextualizeWithin1 shiftInOxpr0 bicontextualizeWithin ctx

-- Run the normalization operation.
normalizeOp :: forall w r m a b. Operations w r m a b -> b
normalizeOp (Product (Tuple lz _)) = extract lz

-- Run the typechecking operation.
typecheckOp :: forall w r m a. Operations w r m a ~> Feedback w r m a
typecheckOp (Product (Tuple _ (Compose lz))) = extract lz

-- Normalize an Oxpr (once).
normalizeStep :: forall w r m a.
  Oxpr w r m a -> Oxpr w r m a
normalizeStep = step2D >>> normalizeOp

-- Typecheck an Oxpr (once).
typecheckStep :: forall w r m a.
  Oxpr w r m a -> Feedback w r m a (Oxpr w r m a)
typecheckStep = step2D >>> typecheckOp

-- Unwrap the Expr layer at the top of an Oxpr.
unlayerO :: forall w r m a.
  Oxpr w r m a -> AST.ExprLayerF m a (Oxpr w r m a)
unlayerO = project >>> un Compose >>> extract >>> unEnvT >>> unwrap

-- Modify the Expr layer at the top of an Oxpr.
overlayerO :: forall w r m a.
  (AST.ExprLayerF m a (Oxpr w r m a) -> AST.ExprLayerF m a (Oxpr w r m a)) ->
  Oxpr w r m a -> Oxpr w r m a
overlayerO = mapR <<< over Compose <<< map <<< mapEnvT <<< over ERVF

-- Add the locations to an expression with locations, starting with the given
-- one at top, and adapting the locations to the tree (i.e. adding LocationWithin).
originateFrom :: forall m a. FunctorWithIndex String m =>
  L m a -> Expr m a -> Lxpr m a
originateFrom = flip <<< cata <<< flip $ go where
  go loc e = embed $ EnvT $ Tuple loc $ (((e)))
    # mapWithIndex \i' -> (#) $ Loc.move (_S::S_ "within") i' <$> loc

-- Same drill, but for a tree that already has locations.
alsoOriginateFrom :: forall m a. FunctorWithIndex String m =>
  L m a -> Lxpr m a -> Lxpr m a
alsoOriginateFrom = flip <<< cata <<< flip $ go where
  go loc (EnvT (Tuple f e)) = embed $ EnvT $ Tuple (loc <> f) $ (((e)))
    # mapWithIndex \i' -> (#) $ Loc.move (_S::S_ "within") i' <$> loc

topLoc :: forall w r m a. Oxpr w r m a -> L m a
topLoc = project >>> un Compose >>> extract >>> env

alsoOriginateFromO :: forall w r m a. FunctorWithIndex String m =>
  L m a -> Oxpr w r m a -> Oxpr w r m a
alsoOriginateFromO = mapR <<< over Compose <<< go where
  go loc e =
    Cofree.deferCofree \_ -> Tuple (Cofree.head e) (Cofree.tail e)
    # bimap
      do mapEnv (loc <> _) >>> mapEnvT (mapWithIndex \i' -> mapR $ over Compose $ go $ Loc.move (_S::S_ "within") i' <$> loc)
      do bitransProduct (map (go (Loc.step (_S::S_ "normalize") <$> loc))) (map (go (Loc.step (_S::S_ "typecheck") <$> loc)))

-- Typecheck an Ocpr by giving it a context. Returns an Oxpr.
typecheckStepCtx :: forall w r m a. FunctorWithIndex String m =>
  BiContext (Oxpr w r m a) -> Ocpr w r m a -> Feedback w r m a (Oxpr w r m a)
typecheckStepCtx ctx = typecheckOp <<< step2D <<< bicontextualizeWithin ctx

-- Turn an Ocpr into an Oxpr by giving it a context at the top-level
-- (which gets adapted as necessary through the layers).
bicontextualizeWithin :: forall w r m a. FunctorWithIndex String m =>
  BiContext (Oxpr w r m a) ->
  Ocpr w r m a -> Oxpr w r m a
bicontextualizeWithin = flip <<< cata <<< flip $ \ctx -> (<<<) In $
  over Compose $ hoistCofree (runReaderT <@> ctx) >>> do
    map $ mapEnvT $ _Newtype $ bicontextualizeWithin1 shiftInOxpr0 (#) ctx

-- Adapt the context for how it should go through one layer.
bicontextualizeWithin1 :: forall m a node node'.
  (String -> node' -> node') -> -- shift in a name
  (BiContext node' -> node -> node') ->
  BiContext node' ->
  AST.ExprLayerF m a node ->
  AST.ExprLayerF m a node'
bicontextualizeWithin1 shiftIn_node' go ctx = trackIntro case _ of
  Nothing -> go ctx
  Just (Tuple name introed) -> go $
    -- NOTE: shift in the current entry as soon as it becomes part of the context
    -- (so it stays valid even if it references the name being shift in)
    Dhall.Context.insert name (join bimap (shiftIn_node' name <<< go ctx) introed) $
      -- Also shift in the remaining parts of the context
      join bimap (shiftIn_node' name) <$> ctx

substcontextualizeWithin1 :: forall m a node node'.
  (String -> node' -> node') -> -- shift in a name
  (SubstContext node' -> node -> node') ->
  SubstContext node' ->
  AST.ExprLayerF m a node ->
  AST.ExprLayerF m a node'
substcontextualizeWithin1 shiftIn_node' go ctx = trackIntro case _ of
  Nothing -> go ctx
  Just (Tuple name introed) -> go $
    Dhall.Context.insert name (map (shiftIn_node' name <<< go ctx) $ theseLeft introed) $
      map (shiftIn_node' name) <$> ctx

-- Substitute any variables available in the context (via `Let` bindings),
-- return `Left` when there is a substitution, or recursing with the provided
-- function (adapting context).
substContext1 :: forall m a node node'.
  (String -> node' -> node') -> -- shift in a name
  (SubstContext node' -> node -> node') ->
  SubstContext node' ->
  AST.ExprLayerF m a node ->
  Either node' (AST.ExprLayerF m a node')
substContext1 shiftIn_node' go ctx =
  substcontextualizeWithin1 shiftIn_node' go ctx >>>
  subst1 ctx

subst1 :: forall m a node.
  SubstContext node ->
  AST.ExprLayerF m a node ->
  Either node (AST.ExprLayerF m a node)
subst1 ctx =
  let
    lookup (AST.V x n) = Dhall.Context.lookup x n ctx >>= identity
    obtain = VariantF.on (_S::S_ "Var") (unwrap >>> lookup) (pure Nothing)
  in obtain >>= case _ of
    Just e -> \_ -> Left e
    _      -> \e -> Right e

-- Substitute a context all the way down an Lxpr, snowballing as it goes
-- (i.e., `Let` bindings introduced in it are also substitute).
-- FIXME: make sure entries in context are substitute in their own context too?
substContextLxpr :: forall m a. FunctorWithIndex String m =>
  SubstContext (Lxpr m a) ->
  Lxpr m a -> Lxpr m a
substContextLxpr ctx e = alsoOriginateFrom (Loc.step (_S::S_ "substitute") <$> extract e) $
  (#) ctx $ (((e))) # cata \(EnvT (Tuple loc (ERVF layer))) ctx' ->
    case substContext1 shiftInLxpr0 (#) ctx' layer of
      Left e' -> e'
      Right layer' -> embed $ EnvT $ Tuple loc $ ERVF layer'

-- FIXME: make sure entries in context are substitute in their own context too?
substContextOxpr :: forall w r m a. FunctorWithIndex String m =>
  SubstContext (Oxpr w r m a) ->
  Oxpr w r m a -> Oxpr w r m a
substContextOxpr ctx e = alsoOriginateFromO (Loc.step (_S::S_ "substitute") <$> topLoc e) $
  (mapR $ over Compose $ go ctx) e where
    go ctx' e' = Cofree.deferCofree \_ ->
      case go1 ctx' (Cofree.head e') of
        Left (In (Compose e'')) -> (Tuple <$> Cofree.head <*> Cofree.tail) e''
        Right layer' -> Tuple layer' $
          bitransProduct (map (go ctx)) (map (go ctx)) (Cofree.tail e')
    go1 ctx' (EnvT (Tuple loc (ERVF layer))) =
      case substContext1 shiftInOxpr0 (mapR <<< over Compose <<< go) ctx' layer of
        Left e' -> Left $ e'
        Right layer' -> Right $ EnvT $ Tuple loc $ ERVF layer'

-- Substitute context all the way down an Expr.
-- FIXME: make sure entries in context are substitute in their own context too?
substContextExpr :: forall m a.
  SubstContext (Expr m a) ->
  Expr m a -> Expr m a
substContextExpr = flip $ cata \(ERVF layer) ctx ->
  case substContext1 (\name -> shift 1 (AST.V name 0)) (#) ctx layer of
    Left e -> e
    Right layer' -> embed $ ERVF layer'

-- Originate from ... itself. Profound.
newborn :: forall m a. FunctorWithIndex String m =>
  Expr m a -> Lxpr m a
newborn e0 = e0 # originateFrom (pure (Tuple empty (Just e0)))

-- Wrap an Lxpr layer, prserving and augmenting the existing locations
-- from the new root.
newmother :: forall m a. FunctorWithIndex String m =>
  AST.ExprLayerF m a (Lxpr m a) -> Lxpr m a
newmother e0 =
  let e_ = AST.embedW $ e0 <#> denote
  in embed $ EnvT $ Tuple (pure (Tuple empty (Just e_))) $ wrap e0
    # mapWithIndex \i -> alsoOriginateFrom (pure (Loc.move (_S::S_ "within") i (Tuple empty (Just e_))))

denote :: forall m a s.
  Ann m a s -> Expr m a
denote = transCata unEnvT

-- Oxpr -> Expr
plain ::
  forall t w m a s.
    Comonad w =>
    Recursive t (Compose w (EnvT s (AST.ExprRowVF m a))) =>
  t -> Expr m a
plain = head2D >>> denote

runLxprAlg :: forall m a i. FunctorWithIndex String m =>
  (
    i ->
    { unlayer :: Lxpr m a -> AST.ExprLayerF m a (Lxpr m a)
    , overlayer :: OverCases (AST.ExprLayerRow m a) (Lxpr m a)
    , recurse :: i -> Lxpr m a -> Identity (Lxpr m a)
    , layer :: AST.ExprLayerF m a (Lxpr m a) -> Lxpr m a
    } -> Lxpr m a -> Identity (Lxpr m a)
  ) ->
  i -> Lxpr m a -> Lxpr m a
runLxprAlg alg i e = un Identity $ runLxprAlgM alg i e

runLxprAlgM :: forall f m a i. FunctorWithIndex String m => Functor f =>
  (
    i ->
    { unlayer :: Lxpr m a -> AST.ExprLayerF m a (Lxpr m a)
    , overlayer :: OverCasesM f (AST.ExprLayerRow m a) (Lxpr m a)
    , recurse :: i -> Lxpr m a -> f (Lxpr m a)
    , layer :: AST.ExprLayerF m a (Lxpr m a) -> Lxpr m a
    } -> Lxpr m a -> f (Lxpr m a)
  ) ->
  i -> Lxpr m a -> f (Lxpr m a)
runLxprAlgM alg = go where
  go i e = alg i
    { unlayer: project >>> unEnvT >>> unwrap
    , overlayer: OverCasesM $ traverseR <<< travEnvT <<< N.traverse ERVF
    , recurse: go
    , layer: newmother
    } e
  travEnvT f (EnvT (Tuple e x)) = EnvT <<< Tuple e <$> f x

runOxprAlg :: forall w r m a i.
  (
    i ->
    { unlayer :: Oxpr w r m a -> AST.ExprLayerF m a (Oxpr w r m a)
    , overlayer :: OverCases (AST.ExprLayerRow m a) (Oxpr w r m a)
    , recurse :: i -> Oxpr w r m a -> Identity (Oxpr w r m a)
    } -> Oxpr w r m a -> Identity (Oxpr w r m a)
  ) ->
  i -> Oxpr w r m a -> Oxpr w r m a
runOxprAlg alg = go where
  go i e = un Identity $ alg i
    { unlayer: unlayerO
    , overlayer: OverCasesM (map pure <<< overlayerO <<< map extract)
    , recurse: map Identity <<< go
    } e

freeInOxpr :: forall w r m a. Foldable m => Var -> Oxpr w r m a -> Disj Boolean
freeInOxpr = flip $ cata $ un Compose >>> extract >>> unEnvT >>> unwrap >>> freeInAlg

freeInLxpr :: forall m a. Foldable m => Var -> Lxpr m a -> Disj Boolean
freeInLxpr = flip $ cata $ unEnvT >>> unwrap >>> freeInAlg

shiftLxpr :: forall m a. FunctorWithIndex String m =>
  Int -> Var -> Lxpr m a -> Lxpr m a
shiftLxpr delta variable e = alsoOriginateFrom (Loc.move (_S::S_ "shift") { delta, variable } <$> extract e) $
  (((e))) #
    runLxprAlg (Variant.case_ # shiftAlgG)
      (Variant.inj (_S::S_ "shift") { delta, variable })

shiftInLxpr :: forall m a. FunctorWithIndex String m =>
  Var -> Lxpr m a -> Lxpr m a
shiftInLxpr = shiftLxpr 1

shiftInLxpr0 :: forall m a. FunctorWithIndex String m =>
  String -> Lxpr m a -> Lxpr m a
shiftInLxpr0 v = shiftInLxpr (AST.V v 0)

shiftOutLxpr :: forall m a. FunctorWithIndex String m =>
  Var -> Lxpr m a -> Lxpr m a
shiftOutLxpr = shiftLxpr (-1)

tryShiftOutLxpr :: forall m a. TraversableWithIndex String m =>
  Var -> Lxpr m a -> Maybe (Lxpr m a)
tryShiftOutLxpr v e | un Disj (freeInLxpr v e) = Nothing
tryShiftOutLxpr v e = Just (shiftOutLxpr v e)

tryShiftOut0Lxpr :: forall m a. TraversableWithIndex String m =>
  String -> Lxpr m a -> Maybe (Lxpr m a)
tryShiftOut0Lxpr v = tryShiftOutLxpr (AST.V v 0)

shiftOxpr :: forall w r m a. Int -> Var -> Oxpr w r m a -> Oxpr w r m a
shiftOxpr delta variable = runOxprAlg (Variant.case_ # shiftAlgG) $
  Variant.inj (_S::S_ "shift") { delta, variable }

shiftInOxpr :: forall w r m a. Var -> Oxpr w r m a -> Oxpr w r m a
shiftInOxpr = shiftOxpr 1

shiftInOxpr0 :: forall w r m a. String -> Oxpr w r m a -> Oxpr w r m a
shiftInOxpr0 v = shiftInOxpr (AST.V v 0)

shiftOutOxpr :: forall w r m a. Var -> Oxpr w r m a -> Oxpr w r m a
shiftOutOxpr = shiftOxpr (-1)

tryShiftOutOxpr :: forall w r m a. Foldable m => Var -> Oxpr w r m a -> Maybe (Oxpr w r m a)
tryShiftOutOxpr v e | un Disj (freeInOxpr v e) = Nothing
tryShiftOutOxpr v e = Just (shiftOutOxpr v e)

tryShiftOut0Oxpr :: forall w r m a. Foldable m => String -> Oxpr w r m a -> Maybe (Oxpr w r m a)
tryShiftOut0Oxpr v = tryShiftOutOxpr (AST.V v 0)

normalizeLxpr :: forall m a. StrMapIsh m => Eq a => Lxpr m a -> Lxpr m a
normalizeLxpr e = alsoOriginateFrom (Loc.step (_S::S_ "normalize") <$> extract e) $
  (extract <<< extract <<< unwrap) $
    -- TODO: use substLxpr and shiftLxpr here
    runLxprAlgM (Variant.case_ # Dhall.Normalize.normalizeWithAlgGW mempty)
      (Variant.inj (_S::S_ "normalize") mempty) e

{-
locateO :: forall w r m a. Eq a => StrMapIsh m =>
  (a -> FeedbackE w ( "Not found" :: ExprRowVFI | r ) m a (Expr m a)) ->
  BiContext (OxprE w ( "Not found" :: ExprRowVFI | r ) m a) ->
  ExprLocation m a -> OxprE w ( "Not found" :: ExprRowVFI | r ) m a ->
  FeedbackE w ( "Not found" :: ExprRowVFI | r ) m a
    (OxprE w ( "Not found" :: ExprRowVFI | r ) m a)
locateO tpa ctx =
  let
    tcingFrom foc = typecheckSketch (typecheckAlgebra tpa) <<< originateFrom foc
    tcingFromIn foc ctx' = tcingFrom foc >>> bicontextualizeWithin ctx'
    tcingFromHere foc = tcingFromIn foc ctx
    tcingFromSelfHere e = tcingFromHere (pure (Tuple empty e)) e
  in case _ of
    MainExpression -> pure
    Place e -> pure (pure (tcingFromSelfHere e))
    Substituted loc -> locateO tpa ctx loc >>> map (substContextOxpr (theseLeft <$> ctx))
    NormalizeLocation loc -> locateO tpa ctx loc >>> map normalizeStep
    TypeOfLocation loc -> locateO tpa ctx loc >=> typecheckStep
    Shifted d v loc -> locateO tpa ctx loc >>> map (shiftOxpr d v)
    LocationWithin i loc -> locateO tpa ctx loc >=> \e -> V.liftW $
      e # unlayerO # ERVF # preview (_ix (extract i)) # do
        V.note $ TypeCheckError
          { location: pure loc
          , tag: Variant.inj (_S::S_ "Not found") (extract i)
          }

locateE :: forall w r m a. Eq a => StrMapIsh m =>
  (a -> Expr m a) ->
  BiContext (Expr m a) ->
  ExprLocation m a -> Expr m a ->
  FeedbackE w ( "Not found" :: ExprRowVFI | r ) m a (Expr m a)
locateE tpa ctx =
  case _ of
    MainExpression -> pure
    Place e -> pure (pure e)
    Substituted loc -> locateE tpa ctx loc >>> map (substContextExpr (theseLeft <$> ctx))
    NormalizeLocation loc -> locateE tpa ctx loc >>> map Dhall.Normalize.normalize
    TypeOfLocation loc -> \e -> do
      e' <- locateE tpa ctx loc e
      ctx' <- ctx # reconstituteCtx \ctx' -> case _ of
        This val -> typeWithA tpa ctx' val
        That ty -> pure ty
        Both _ ty -> pure ty
      typeWithA tpa ctx' e'
    Shifted d v loc -> locateE tpa ctx loc >>> map (Variables.shift d v)
    LocationWithin i loc -> locateE tpa ctx loc >=> \e -> V.liftW $
      e # project # preview (_ix (extract i)) # do
        V.note $ TypeCheckError
          { location: pure loc
          , tag: Variant.inj (_S::S_ "Not found") (extract i)
          }
-}

newtype Inconsistency a = Inconsistency (NonEmpty (NonEmpty List) a)
derive instance newtypeInconsistency :: Newtype (Inconsistency a) _
derive newtype instance functorInconsistency :: Functor Inconsistency
derive newtype instance foldableInconsistency :: Foldable Inconsistency
derive newtype instance foldable1Inconsistency :: Foldable1 Inconsistency
derive newtype instance traversableInconsistency :: Traversable Inconsistency
-- derive newtype instance traversable1Inconsistency :: Traversable1 Inconsistency
tabulateGroupings :: forall k v.
  (v -> v -> Boolean) ->
  List { key :: k, value :: v } -> List (NonEmptyList { key :: k, value :: v })
tabulateGroupings egal = go empty where
  go accum = case _ of
    List.Nil -> empty
    List.Cons v0 rest -> go (insertGrouping v0 accum) rest
  insertGrouping v0 = case _ of
    List.Nil -> pure (pure v0)
    List.Cons vn accum
      | egal (extract vn).value v0.value ->
        List.Cons (NEL.cons v0 vn) accum
      | otherwise -> List.Cons vn (insertGrouping v0 accum)

consistency :: forall a. List a -> Maybe (Inconsistency a)
consistency (List.Cons a0 (List.Cons a1 an)) =
  pure $ Inconsistency $ a0 :| a1 :| an
consistency _ = empty

ensureConsistency :: forall m f v. Applicative f => StrMapIsh m =>
  (v -> v -> Boolean) ->
  (Inconsistency (NonEmptyList { key :: String, value :: v }) -> f Void) ->
  m v -> f Unit
ensureConsistency egal error = traverse_ error
  <<< consistency
  <<< tabulateGroupings egal
  <<< map (uncurry { key: _, value: _ })
  <<< StrMapIsh.toUnfoldable

ensureNodupes ::
  forall f m v i.
    Applicative f =>
    FoldableWithIndex i m =>
    Ord i =>
  (NonEmptyList i -> f Void) ->
  m v -> f Unit
ensureNodupes error = traverse_ error <<< findDupes

findDupes :: forall i m v. Ord i => FoldableWithIndex i m =>
  m v -> Maybe (NonEmptyList i)
findDupes = (foldMap (pure <<< pure) :: Array i -> Maybe (NonEmptyList i))
  <<< Array.mapMaybe (\a -> if NEA.length a > 1 then Just (NEA.head a) else Nothing)
  <<< Array.group
  <<< Array.sort
  <<< foldMapWithIndex (\i _ -> [i])

type Errors r =
  ( "Not a function" :: Unit
  , "Type mismatch" :: Unit
  , "Invalid predicate" :: Unit
  , "If branch mismatch" :: Unit
  , "If branch must be term" :: Boolean
  , "Invalid list type" :: Unit
  , "Missing list type" :: Unit
  , "Invalid list element" :: Int
  , "Mismatched list elements" :: Int
  , "Cannot append non-list" :: Boolean
  , "Cannot interpolate" :: Natural
  , "List append mismatch" :: Unit
  , "Invalid optional type" :: Unit
  , "Invalid optional element" :: Unit
  , "Invalid `Some`" :: Unit
  , "Duplicate record fields" :: NonEmptyList String
  , "Invalid field type" :: String
  , "Inconsistent field types" :: Inconsistency (NonEmptyList String)
  , "Duplicate union fields" :: NonEmptyList String
  , "Invalid alternative type" :: String
  , "Must combine a record" :: Tuple (List String) Boolean
  , "Record kind mismatch" :: List String
  , "Oops" :: Unit
  , "Must merge a record" :: Unit
  , "Must merge a union" :: Unit
  , "Missing merge type" :: Unit
  , "Handler not a function" :: String
  , "Dependent handler function" :: String
  , "Missing handler" :: Set Unit
  , "Handler input type mismatch" :: String
  , "Handler output type mismatch" :: String
  , "Unused handlers" :: Set Unit
  , "Cannot project" :: Unit
  , "Missing field" :: String
  , "Invalid input type" :: Unit
  , "Invalid output type" :: Unit
  , "No dependent types" :: Unit
  , "Unbound variable" :: Var
  , "Annotation mismatch" :: Unit
  , "`Kind` has no type" :: Unit
  , "Unexpected type" :: Boolean
  , "Cannot access" :: String
  , "Constructors requires a union type" :: Unit
  | r
  )
type FeedbackE w r m a = Feedback w (Errors r) m a
type OxprE w r m a = Oxpr w (Errors r) m a

reconstituteCtx :: forall a b m. Bind m => Applicative m =>
  (Context b -> a -> m b) -> Context a -> m (Context b)
reconstituteCtx = reconstituteCtxFrom Dhall.Context.empty

-- TODO: MonadRec?
-- TODO: convince myself that no shifting needs to occur here
reconstituteCtxFrom :: forall a b m. Bind m => Applicative m =>
  Context b -> (Context b -> a -> m b) -> Context a -> m (Context b)
reconstituteCtxFrom ctx0 f = foldr f' (pure ctx0) <<< un Context <<< unshift where
  -- TODO: shift?
  unshift = identity
  f' (Tuple name a) mctx = do
    ctx <- mctx
    b <- f ctx a
    -- TODO: shift?
    pure $ Dhall.Context.insert name b ctx

{-| Generalization of `typeWith` that allows type-checking the `Embed`
    constructor with custom logic
-}
typeWithA :: forall w r m a.
  Eq a => StrMapIsh m =>
  Typer m a ->
  Context (Expr m a) ->
  Expr m a ->
  FeedbackE w r m a (Expr m a)
typeWithA tpa ctx0 e0 = do
  let
    tcingFrom foc = typecheckSketch (typecheckAlgebra (pure <<< tpa)) <<< originateFrom foc
    -- Convert an Expr to an Oxpr and typecheck in the given context
    -- (which must consist of Oxprs)
    tcingIn :: BiContext (OxprE w r m a) -> Expr m a -> FeedbackE w r m a (OxprE w r m a)
    tcingIn ctx e =
      let
        e' = tcingFrom (pure (Tuple empty (Just e))) e # bicontextualizeWithin ctx
      in e' <$ typecheckStep e'
  -- convert ctx0 and e0 to Oxprs
  ctxO <- reconstituteCtx (\ctx ty -> That <$> tcingIn ctx ty) ctx0
  let eO = tcingFrom (pure (Tuple empty Nothing)) e0
  -- and run typechecking on eO
  plain <$> typecheckStepCtx ctxO eO

typecheckAlgebra :: forall w r m a. Eq a => StrMapIsh m =>
  (a -> FeedbackE w r m a (Expr m a)) ->
  WithBiCtx (LxprF m a) (OxprE w r m a) -> FeedbackE w r m a (Lxpr m a)
typecheckAlgebra tpa (WithBiCtx ctx (EnvT (Tuple loc layer))) = unwrap layer # VariantF.match
  let
    errorHere ::
      forall sym t r' b.
        IsSymbol sym =>
        R.Cons sym t r' (Errors r) =>
      SProxy sym ->
      t ->
      FeedbackE w r m a b
    errorHere sym v = V.liftW $ V.erroring $ TypeCheckError
      { location: loc
      , tag: Variant.inj sym v
      }

    noteHere ::
      forall sym t r' b.
        IsSymbol sym =>
        R.Cons sym t r' (Errors r) =>
      SProxy sym ->
      t ->
      Maybe b ->
      FeedbackE w r m a b
    noteHere sym v = (<<<) V.liftW $ V.note $ TypeCheckError
      { location: loc
      , tag: Variant.inj sym v
      }

    mkFunctor f a = mk (_S::S_ "App") $
      Pair (newborn f) a
    mk :: forall sym f r'.
      Functor f =>
      IsSymbol sym =>
      R.Cons sym (FProxy f) r' (AST.ExprLayerRow m a) =>
      SProxy sym ->
      f (Lxpr m a) ->
      Lxpr m a
    mk sym = newmother <<< VariantF.inj sym
    ensure' :: forall sym f r'.
      IsSymbol sym =>
      R.Cons sym (FProxy f) r' (AST.ExprLayerRow m a) =>
      SProxy sym ->
      OxprE w r m a ->
      (Unit -> FeedbackE w r m a Void) ->
      FeedbackE w r m a (f (OxprE w r m a))
    ensure' s ty error =
      let nf_ty = normalizeStep ty in
      unlayerO nf_ty # VariantF.on s pure
        \_ -> absurd <$> error unit
    ensureConst ::
      OxprE w r m a ->
      (Unit -> FeedbackE w r m a Void) ->
      FeedbackE w r m a Const
    ensureConst expr error = do
      ty <- typecheckStep expr
      unwrap <$> ensure' (_S::S_ "Const") ty error

    checkEq ::
      OxprE w r m a -> OxprE w r m a ->
      (Unit -> FeedbackE w r m a Void) ->
      FeedbackE w r m a Unit
    checkEq ty0 ty1 error =
      let
        Pair ty0' ty1' = Pair ty0 ty1 <#>
          normalizeStep >>> plain >>> AST.unordered
      in
      when (ty0' /= ty1') $
        absurd <$> error unit
    checkEqL ::
      OxprE w r m a -> OxprE w r m a ->
      (Unit -> FeedbackE w r m a Void) ->
      FeedbackE w r m a (OxprE w r m a)
    checkEqL ty0 ty1 error = suggest ty0 $ checkEq ty0 ty1 error
    checkEqR ::
      OxprE w r m a -> OxprE w r m a ->
      (Unit -> FeedbackE w r m a Void) ->
      FeedbackE w r m a (OxprE w r m a)
    checkEqR ty0 ty1 error = suggest ty1 $ checkEq ty0 ty1 error

    onConst :: forall x.
      (x -> FeedbackE w r m a (Expr m a)) ->
      Const.Const x (OxprE w r m a) ->
      FeedbackE w r m a (Lxpr m a)
    onConst f (Const.Const c) = f c <#> newborn
    always :: forall y. Expr m a -> y -> FeedbackE w r m a (Lxpr m a)
    always b _ = pure $ newborn $ b
    aType :: forall x. Const.Const x (OxprE w r m a) -> FeedbackE w r m a (Lxpr m a)
    aType = always $ AST.mkType
    aFunctor :: forall x. Const.Const x (OxprE w r m a) -> FeedbackE w r m a (Lxpr m a)
    aFunctor = always $ AST.mkArrow AST.mkType AST.mkType
    a0 = AST.mkVar (AST.V "a" 0)

    -- TODO: This will need to become aware of AST holes
    -- Check a binary operation (`Pair` functor) against a simple, static,
    -- *normalize* type `t`.
    checkBinOp ::
      Expr m a ->
      Pair (OxprE w r m a) ->
      FeedbackE w r m a (Lxpr m a)
    checkBinOp t p = suggest (newborn t) $ forWithIndex_ p $
      -- t should be simple enough that alphaNormalize is unnecessary
      \side operand -> typecheckStep operand >>= normalizeStep >>> case _ of
        ty_operand | t == plain ty_operand -> pure unit
          | otherwise -> errorHere
            (_S::S_ "Unexpected type") side

    naturalEnc =
      AST.mkForall "natural" $
        let natural = AST.mkVar (AST.V "natural" 0) in
        AST.mkPi "succ" (AST.mkArrow natural natural) $
          AST.mkPi "zero" natural $
            natural

    listEnc a =
      AST.mkForall "list" $
        let list = AST.mkVar (AST.V "list" 0) in
        AST.mkPi "cons" (AST.mkArrow a $ AST.mkArrow list list) $
          AST.mkPi "nil" list $
            list

    optionalEnc a =
      AST.mkForall "optional" $
        let optional = AST.mkVar (AST.V "optional" 0) in
        AST.mkPi "some" (AST.mkArrow a optional) $
          AST.mkPi "none" optional $
            optional

    ensure :: forall sym f r'.
      IsSymbol sym =>
      R.Cons sym (FProxy f) r' (AST.ExprLayerRow m a) =>
      SProxy sym ->
      OxprE w r m a ->
      (Unit -> FeedbackE w r m a Void) ->
      FeedbackE w r m a (f (OxprE w r m a))
    ensure s expr error = do
      ty <- typecheckStep expr
      ensure' s ty error

    -- Ensure that the passed `expr` is a term; i.e. the type of its type
    -- is `Type`. Returns the type of the `expr`.
    ensureTerm ::
      OxprE w r m a ->
      (Unit -> FeedbackE w r m a Void) ->
      FeedbackE w r m a (OxprE w r m a)
    ensureTerm expr error = do
      ty <- typecheckStep expr
      ty <$ ensureType ty error

    -- Ensure that the passed `ty` is a type; i.e. its type is `Type`.
    ensureType ::
      OxprE w r m a ->
      (Unit -> FeedbackE w r m a Void) ->
      FeedbackE w r m a Unit
    ensureType ty error = do
      kind <- typecheckStep ty
      ensure' (_S::S_ "Const") kind error >>= case _ of
        Const.Const Type -> pure unit
        _ -> absurd <$> error unit
  in
  { "Const": unwrap >>> \c ->
      axiom c <#> newborn <<< AST.mkConst #
        noteHere (_S::S_ "`Kind` has no type") unit
  , "Var": unwrap >>> \v@(AST.V name idx) ->
      case Dhall.Context.lookup name idx ctx of
        -- NOTE: this should always succeed, since the body is checked only
        -- after the `Let` value succeeds.
        Just (This value) -> head2D <$> typecheckStep value
        Just (That ty) -> pure $ head2D ty
        Just (Both _ ty) -> pure $ head2D ty
        Nothing ->
          errorHere (_S::S_ "Unbound variable") v
  , "Lam": \(AST.BindingBody name ty body) -> do
      kA <- ensureConst ty
        (errorHere (_S::S_ "Invalid input type"))
      ty_body <- typecheckStep body
      kB <- ensureConst ty_body
        (errorHere (_S::S_ "Invalid output type"))
      _ <- rule kA kB #
        noteHere (_S::S_ "No dependent types") unit
      pure $ mk(_S::S_"Pi") (AST.BindingBody name (head2D ty) (head2D ty_body))
  , "Pi": \(AST.BindingBody name ty ty_body) -> do
      kA <- ensureConst ty
        (errorHere (_S::S_ "Invalid input type"))
      kB <- ensureConst ty_body
        (errorHere (_S::S_ "Invalid output type"))
      map (newborn <<< AST.mkConst) $ rule kA kB #
        noteHere (_S::S_ "No dependent types") unit
  , "Let": \(AST.LetF name mty value expr) -> do
      ty0 <- typecheckStep value
      ty <- fromMaybe ty0 <$> for mty \ty' -> do
        _ <- typecheckStep ty'
        checkEqR ty0 ty'
          (errorHere (_S::S_ "Annotation mismatch"))
      head2D <$> typecheckStep expr
  , "App": \(AST.Pair f a) ->
      let
        checkFn = ensure (_S::S_ "Pi") f
          (errorHere (_S::S_ "Not a function"))
        checkArg (AST.BindingBody name aty0 rty) aty1 =
          let shift = tryShiftOut0Lxpr name (head2D rty) in
          if Dhall.Core.judgmentallyEqual (plain aty0) (plain aty1)
            then pure case shift of
              Nothing -> mk(_S::S_"App") $ Pair
                do mk(_S::S_"Lam") (head2D <$> AST.BindingBody name aty0 rty)
                do head2D a
              Just rty' -> rty'
            else do
              -- SPECIAL!
              -- Recovery case: if the variable is unused in the return type
              -- then this is a non-dependent function
              -- and its return type can be suggested
              -- even if its argument does not have the right type
              errorHere (_S::S_ "Type mismatch") unit # case shift of
                Nothing -> identity
                Just rty' -> suggest rty'
      in join $ checkArg <$> checkFn <*> typecheckStep a
  , "Annot": \(AST.Pair expr ty) ->
      map head2D $ join $ checkEqR
        <$> typecheckStep expr
        <@> ty
        <@> errorHere (_S::S_ "Annotation mismatch")
        <* typecheckStep ty
  , "Bool": identity aType
  , "BoolLit": always $ AST.mkBool
  , "BoolAnd": checkBinOp AST.mkBool
  , "BoolOr": checkBinOp AST.mkBool
  , "BoolEQ": checkBinOp AST.mkBool
  , "BoolNE": checkBinOp AST.mkBool
  , "BoolIf": \(AST.Triplet c t f) ->
      ensure (_S::S_ "Bool") c
        (errorHere (_S::S_ "Invalid predicate")) *> do
      map head2D $ join $ checkEqL
          <$> ensureTerm t
            (errorHere (_S::S_ "If branch must be term") <<< const false)
          <*> ensureTerm f
            (errorHere (_S::S_ "If branch must be term") <<< const true)
          <@> errorHere (_S::S_ "If branch mismatch")
  , "Natural": identity aType
  , "NaturalLit": always $ AST.mkNatural
  , "NaturalFold": always $ AST.mkArrow AST.mkNatural naturalEnc
  , "NaturalBuild": always $ AST.mkArrow naturalEnc AST.mkNatural
  , "NaturalIsZero": always $ AST.mkArrow AST.mkNatural AST.mkBool
  , "NaturalEven": always $ AST.mkArrow AST.mkNatural AST.mkBool
  , "NaturalOdd": always $ AST.mkArrow AST.mkNatural AST.mkBool
  , "NaturalToInteger": always $ AST.mkArrow AST.mkNatural AST.mkInteger
  , "NaturalShow": always $ AST.mkArrow AST.mkNatural AST.mkText
  , "NaturalPlus": checkBinOp AST.mkNatural
  , "NaturalTimes": checkBinOp AST.mkNatural
  , "Integer": identity aType
  , "IntegerLit": always $ AST.mkInteger
  , "IntegerShow": always $ AST.mkArrow AST.mkInteger AST.mkText
  , "IntegerToDouble": always $ AST.mkArrow AST.mkInteger AST.mkDouble
  , "Double": identity aType
  , "DoubleLit": always $ AST.mkDouble
  , "DoubleShow": always $ AST.mkArrow AST.mkDouble AST.mkText
  , "Text": identity aType
  , "TextLit": \things -> suggest (newborn AST.mkText) $
      forWithIndex_ things \i expr -> ensure (_S::S_ "Text") expr
        (errorHere (_S::S_ "Cannot interpolate") <<< const i)
  , "TextAppend": checkBinOp AST.mkText
  , "List": identity aFunctor
  , "ListLit": \(Product (Tuple mty lit)) -> mkFunctor AST.mkList <<< head2D <$> do
      -- get the assumed type of the list
      (ty :: OxprE w r m a) <- case mty of
        -- either from annotation
        Just ty -> suggest ty $
          ensureType ty
            (errorHere (_S::S_ "Invalid list type"))
        -- or from the first element
        Nothing -> case Array.head lit of
          Nothing -> errorHere (_S::S_ "Missing list type") $ unit
          Just item -> do
            ensureTerm item
              (errorHere (_S::S_ "Invalid list type"))
      suggest ty $ forWithIndex_ lit \i item -> do
        ty' <- typecheckStep item
        checkEq ty ty' \_ ->
          case mty of
            Nothing ->
              errorHere (_S::S_ "Invalid list element") $ i
            Just _ ->
              errorHere (_S::S_ "Mismatched list elements") $ i
  , "ListAppend": \p -> mkFunctor AST.mkList <<< head2D <$> do
      AST.Pair ty_l ty_r <- forWithIndex p \side expr -> do
        let error = errorHere (_S::S_ "Cannot append non-list") <<< const side
        expr_ty <- typecheckStep expr
        AST.Pair list ty <- ensure' (_S::S_ "App") expr_ty error
        normalizeStep list # unlayerO #
          VariantF.on (_S::S_ "List") (const (pure unit))
            \_ -> absurd <$> error unit
        pure ty
      checkEqL ty_l ty_r
        (errorHere (_S::S_ "List append mismatch"))
  , "ListBuild": always $ AST.mkForall "a" $
      AST.mkArrow (listEnc a0) (AST.mkApp AST.mkList a0)
  , "ListFold": always $ AST.mkForall "a" $
      AST.mkArrow (AST.mkApp AST.mkList a0) (listEnc a0)
  , "ListLength": always $
      AST.mkForall "a" $ AST.mkArrow
        (AST.mkApp AST.mkList a0) AST.mkNatural
  , "ListHead": always $
      AST.mkForall "a" $ AST.mkArrow
        (AST.mkApp AST.mkList a0) (AST.mkApp AST.mkOptional a0)
  , "ListLast": always $
      AST.mkForall "a" $ AST.mkArrow
        (AST.mkApp AST.mkList a0) (AST.mkApp AST.mkOptional a0)
  , "ListIndexed": always $
      AST.mkForall "a" $
        AST.mkArrow (AST.mkApp AST.mkList a0) $
          AST.mkApp AST.mkList $ AST.mkRecord $ StrMapIsh.fromFoldable
            [Tuple "index" AST.mkNatural, Tuple "value" a0]
  , "ListReverse": always $
      AST.mkForall "a" $ join AST.mkArrow
        (AST.mkApp AST.mkList a0)
  , "Optional": identity aFunctor
  , "None": always $
      AST.mkPi "A" AST.mkType $
        AST.mkApp AST.mkOptional (AST.mkVar (AST.V "A" 0))
  , "OptionalLit": \(Product (Tuple (Identity ty) mexpr)) -> do
      ensureType ty
        (errorHere (_S::S_ "Invalid optional type"))
      suggest (mkFunctor AST.mkOptional (head2D ty)) $
        for_ mexpr \expr -> do
          join $ checkEq ty
            <$> typecheckStep expr
            <@> (errorHere (_S::S_ "Invalid optional element"))
  , "Some": unwrap >>> \a ->
      mkFunctor AST.mkOptional <<< head2D <$> ensureTerm a
        (errorHere (_S::S_ "Invalid `Some`"))
  , "OptionalFold": always $ AST.mkForall "a" $
      AST.mkArrow (AST.mkApp AST.mkOptional a0) (optionalEnc a0)
  , "OptionalBuild": always $ AST.mkForall "a" $
      AST.mkArrow (optionalEnc a0) (AST.mkApp AST.mkOptional a0)
  , "Record": \kts ->
      ensureNodupes
        (errorHere (_S::S_ "Duplicate record fields")) kts
      *> do
        kts' <- forWithIndex kts \field ty -> do
          c <- unwrap <$> ensure (_S::S_ "Const") ty
            (errorHere (_S::S_ "Invalid field type") <<< const field)
          case c of
            Kind ->
              let error _ = errorHere (_S::S_ "Invalid field type") field in
              unlayerO ty # VariantF.on (_S::S_ "Const")
                (unwrap >>> \c' -> when (c /= Type) (error unit))
                (\_ -> error unit)
            _ -> pure unit
          pure { kind: c }
        ensureConsistency (eq `on` _.kind)
          (errorHere (_S::S_ "Inconsistent field types") <<< (map <<< map) _.key) kts'
        pure $ newborn $ AST.mkConst $ maybe Type _.kind $ un First $ foldMap pure kts'
  , "RecordLit": \kvs ->
      ensureNodupes
        (errorHere (_S::S_ "Duplicate record fields")) kvs
      *> do
        kts <- traverse typecheckStep kvs
        suggest (mk(_S::S_"Record") (head2D <$> kts)) do
          kts' <- forWithIndex kts \field ty -> do
            c <- unwrap <$> ensure (_S::S_ "Const") ty
              (errorHere (_S::S_ "Invalid field type") <<< const field)
            case c of
              Kind ->
                let error _ = errorHere (_S::S_ "Invalid field type") field in
                unlayerO ty # VariantF.on (_S::S_ "Const")
                  (unwrap >>> \c' -> when (c /= Type) (error unit))
                  (\_ -> error unit)
              _ -> pure unit
            pure { kind: c }
          ensureConsistency (eq `on` _.kind)
            (errorHere (_S::S_ "Inconsistent field types") <<< (map <<< map) _.key) kts'
  , "Union": \kts ->
      ensureNodupes
        (errorHere (_S::S_ "Duplicate union fields")) kts
      *> do
        -- FIXME: should this be the largest of `Type` or `Kind` returned?
        suggest (newborn AST.mkType) $
          forWithIndex_ kts \field ty -> do
            void $ ensure (_S::S_ "Const") ty
              (errorHere (_S::S_ "Invalid alternative type") <<< const field)
  , "UnionLit": \(Product (Tuple (Tuple field expr) kts)) ->
      ensureNodupes
        (errorHere (_S::S_ "Duplicate union fields")) kts
      *> do
        ty <- typecheckStep expr
        let kts' = StrMapIsh.insert field ty kts
        forWithIndex_ kts' \field' kind -> do
          void $ ensure (_S::S_ "Const") kind
            (errorHere (_S::S_ "Invalid alternative type") <<< const field')
        pure $ mk(_S::S_"Union") $ head2D <$> kts'
  , "Combine":
      let
        combineTypes here (p :: Pair (OxprE w r m a)) = do
          AST.Pair { const: constL, kts: ktsL } { const: constR, kts: ktsR } <-
            forWithIndex p \side ty -> do
              kts <- ensure' (_S::S_ "Record") ty
                (errorHere (_S::S_ "Must combine a record") <<< const (Tuple here side))
              kind <- typecheckStep ty
              const <- ensureConst kind
                (errorHere (_S::S_ "Must combine a record") <<< const (Tuple here side))
              pure { kts, const }
          when (constL /= constR) $ errorHere (_S::S_ "Record kind mismatch") $ here
          let combined = StrMapIsh.unionWith (pure pure) ktsL ktsR
          mk(_S::S_"Record") <$> forWithIndex combined \k ->
            case _ of
              Both ktsL' ktsR' ->
                combineTypes (k : here) (AST.Pair ktsL' ktsR')
              This t -> pure (head2D t)
              That t -> pure (head2D t)
      in (=<<) (combineTypes Nil) <<< traverse typecheckStep
  , "CombineTypes":
      let
        combineTypes here (p :: Pair (OxprE w r m a)) = do
          AST.Pair { const: constL, kts: ktsL } { const: constR, kts: ktsR } <-
            forWithIndex p \side ty -> do
              kts <- ensure' (_S::S_ "Record") ty
                (errorHere (_S::S_ "Must combine a record") <<< const (Tuple here side))
              kind <- typecheckStep ty
              const <- ensureConst kind
                (errorHere (_S::S_ "Must combine a record") <<< const (Tuple here side))
              pure { kts, const }
          when (constL /= constR) $ errorHere (_S::S_ "Record kind mismatch") $ here
          let combined = StrMapIsh.unionWith (pure pure) ktsL ktsR
          mk(_S::S_"Record") <$> forWithIndex combined \k ->
            case _ of
              Both ktsL' ktsR' ->
                combineTypes (k : here) (AST.Pair ktsL' ktsR')
              This t -> pure (head2D t)
              That t -> pure (head2D t)
      in combineTypes Nil
  , "Prefer": \p -> do
      AST.Pair { const: constL, kts: ktsL } { const: constR, kts: ktsR } <-
        forWithIndex p \side kvs -> do
          ty <- typecheckStep kvs
          kts <- ensure' (_S::S_ "Record") ty
            (errorHere (_S::S_ "Must combine a record") <<< const (Tuple Nil side))
          k <- typecheckStep ty
          const <- unwrap <$> ensure (_S::S_ "Const") ty
            (errorHere (_S::S_ "Must combine a record") <<< const (Tuple Nil side))
          pure { kts, const }
      when (constL /= constR) $ errorHere (_S::S_ "Record kind mismatch") $ Nil
      let
        preference = Just <<< case _ of
          This a -> a
          That b -> b
          Both a _ -> a
      pure $ mk(_S::S_"Record") $ map head2D $ StrMapIsh.unionWith (pure preference) ktsR ktsL
  , "Merge": \(AST.MergeF handlers cases mty) -> do
      Pair ktsX ktsY <- Pair
        <$> ensure (_S::S_ "Record") handlers
          (errorHere (_S::S_ "Must merge a record"))
        <*> ensure (_S::S_ "Union") cases
          (errorHere (_S::S_ "Must merge a union"))
      let
        ksX = unit <$ ktsX # Set.fromFoldable
        ksY = unit <$ ktsY # Set.fromFoldable
        diffX = Set.difference ksX ksY
        diffY = Set.difference ksY ksX
      -- get the assumed type of the merge result
      ty <- case mty of
        -- either from annotation
        Just ty -> pure ty
        -- or from the first handler
        Nothing -> case un First $ foldMapWithIndex (curry pure) ktsX of
          Nothing -> errorHere (_S::S_ "Missing merge type") $ unit
          Just (Tuple k item) -> do
            AST.BindingBody name _ output <- ensure' (_S::S_ "Pi") item
              (errorHere (_S::S_ "Handler not a function") <<< const k)
            output' <- tryShiftOut0Oxpr name output #
              (noteHere (_S::S_ "Dependent handler function") <<< const k $ unit)
            pure output'
      suggest (head2D ty) ado
        when (not Set.isEmpty diffX)
          (errorHere (_S::S_ "Unused handlers") diffX)
        forWithIndex_ ktsY \k tY -> do
          tX <- StrMapIsh.get k ktsX #
            noteHere (_S::S_ "Missing handler") diffX
          AST.BindingBody name input output <- ensure' (_S::S_ "Pi") tX
            (errorHere (_S::S_ "Handler not a function") <<< const k)
          ado
            checkEq tY input
              (errorHere (_S::S_ "Handler input type mismatch") <<< const k)
            do
              output' <- tryShiftOut0Oxpr name output #
                (noteHere (_S::S_ "Dependent handler function") <<< const k $ unit)
              checkEq ty output'
                (errorHere (_S::S_ "Handler output type mismatch") <<< const k)
          in unit
        in unit
  , "Constructors": \(Identity ty) -> do
      void $ typecheckStep ty
      kts <- ensure (_S::S_ "Union") ty
          \_ -> errorHere (_S::S_ "Constructors requires a union type") $ unit
      pure $ mk(_S::S_"Record") $ kts # mapWithIndex \field ty' ->
        mk(_S::S_"Pi") (AST.BindingBody field (head2D ty') (head2D ty))
  , "Field": \(Tuple field expr) -> do
      tyR <- typecheckStep expr
      let
        error _ = errorHere (_S::S_ "Cannot access") $ field
        handleRecord kts = do
          case StrMapIsh.get field kts of
            Just ty -> pure (head2D ty)
            Nothing -> errorHere (_S::S_ "Missing field") $ field
        handleType kts = do
          case StrMapIsh.get field kts of
            Just ty -> pure $ mk(_S::S_"Pi") $ map head2D $ (AST.BindingBody field ty expr)
            Nothing -> errorHere (_S::S_ "Missing field") $ field
        casing = (\_ -> error unit)
          # VariantF.on (_S::S_ "Record") handleRecord
          # VariantF.on (_S::S_ "Const") \(Const.Const c) ->
              case c of
                Type -> expr # normalizeStep # unlayerO #
                  VariantF.on (_S::S_ "Union") handleType (\_ -> error unit)
                _ -> error unit
      tyR # normalizeStep # unlayerO # casing
  , "Project": \(Tuple (App ks) expr) -> do
      kts <- ensure (_S::S_ "Record") expr
        (errorHere (_S::S_ "Cannot project"))
      mk(_S::S_"Record") <<< map head2D <$> forWithIndex ks \k (_ :: Unit) ->
        StrMapIsh.get k kts #
          (noteHere (_S::S_ "Missing field") k)
  , "ImportAlt": \(Pair l _r) ->
      -- FIXME???
      head2D <$> typecheckStep l
  , "Embed": map (originateFrom (Loc.step (_S::S_ "typecheck") <$> loc)) <<< tpa <<< unwrap
  }

-- The explanation, given as text interspersed with specific places to look at
-- (for the user to read)
explain ::
  forall m a.
    StrMapIsh m =>
  Expr m a ->
  Variant (Errors ()) ->
  AST.TextLitF (ExprLocation m a)
explain origin =
  let errorUnknownError = AST.TextLit "Sorry I don’t know how to explain this error"
      nodeType = AST.projectW origin
  in
  Variant.default errorUnknownError

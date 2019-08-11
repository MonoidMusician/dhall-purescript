module Dhall.TypeCheck where

import Prelude

import Control.Alternative (class Alternative, (<|>))
import Control.Apply (lift2)
import Control.Comonad (class Comonad, extend, extract)
import Control.Comonad.Cofree (Cofree, buildCofree, hoistCofree)
import Control.Comonad.Cofree as Cofree
import Control.Comonad.Env (EnvT(..), mapEnvT, runEnvT)
import Control.Monad.Reader (ReaderT(..), runReaderT)
import Control.Monad.Writer (WriterT(..))
import Control.Plus (empty)
import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Bifoldable (bifoldMap, bifoldl, bifoldr)
import Data.Bifunctor (bimap)
import Data.Bitraversable (bisequence, bitraverse)
import Data.Const as Const
import Data.Either (Either(..))
import Data.Foldable (class Foldable, foldMap, foldl, foldlDefault, foldr, foldrDefault, null, oneOfMap, traverse_)
import Data.FoldableWithIndex (class FoldableWithIndex, anyWithIndex, foldMapWithIndex, forWithIndex_)
import Data.Functor.App (App(..))
import Data.Functor.Compose (Compose(..))
import Data.Functor.Mu (Mu(..))
import Data.Functor.Product (Product(..))
import Data.Functor.Variant (FProxy, SProxy, VariantF)
import Data.Functor.Variant as VariantF
import Data.FunctorWithIndex (class FunctorWithIndex, mapWithIndex)
import Data.Identity (Identity(..))
import Data.Lazy (Lazy, defer)
import Data.Lens (firstOf, has, lastOf, preview)
import Data.Lens.Indexed (asIndex, itraversed)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.List (List(..), (:))
import Data.List as List
import Data.List.NonEmpty (foldMap1)
import Data.List.NonEmpty as NEL
import Data.List.Types (NonEmptyList(..))
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Maybe.First (First(..))
import Data.Monoid.Disj (Disj(..))
import Data.Monoid.Endo (Endo(..))
import Data.Natural (Natural)
import Data.Newtype (class Newtype, over, un, unwrap, wrap)
import Data.Newtype as N
import Data.NonEmpty (NonEmpty, (:|))
import Data.Ord.Max (Max(..))
import Data.Profunctor.Strong ((&&&))
import Data.Semigroup.Foldable (class Foldable1)
import Data.Set (Set)
import Data.Set as Set
import Data.String as String
import Data.Symbol (class IsSymbol)
import Data.These (These(..), theseLeft)
import Data.Traversable (class Traversable, for, sequence, traverse)
import Data.TraversableWithIndex (class TraversableWithIndex, forWithIndex, traverseWithIndex)
import Data.Tuple (Tuple(..), curry, fst, uncurry)
import Data.Variant (Variant)
import Data.Variant as Variant
import Dhall.Context (Context(..))
import Dhall.Context as Dhall.Context
import Dhall.Core (Var(..), alphaNormalize, shift)
import Dhall.Core as Variables
import Dhall.Core.AST (Const(..), Expr, ExprRowVF(..), ExprRowVFI(..), Pair(..), S_, _S, hoistExpr)
import Dhall.Core.AST as AST
import Dhall.Core.AST.Operations.Location (BasedExprDerivation, Derived, Operated, Within, Derivation)
import Dhall.Core.AST.Operations.Location as Loc
import Dhall.Core.AST.Operations.Transformations (OverCases, OverCasesM(..))
import Dhall.Core.Imports.Retrieve (headerType)
import Dhall.Core.Zippers (_ix)
import Dhall.Map (class MapLike)
import Dhall.Map as Dhall.Map
import Dhall.Normalize as Dhall.Normalize
import Dhall.Variables (MaybeIntro(..), alphaNormalizeAlgG, freeInAlg, shiftAlgG, trackIntro)
import Matryoshka (class Corecursive, class Recursive, ana, cata, embed, mapR, project, transCata, traverseR)
import Type.Row (type (+))
import Type.Row as R
import Validation.These as V

axiom :: forall f. Alternative f => Const -> f Const
axiom Type = pure Kind
axiom Kind = pure Sort
axiom Sort = empty

rule :: forall f. Applicative f => Const -> Const -> f Const
rule _ Type = pure Type
rule a b = pure $ max a b

maxConst :: forall f. Foldable f => f Const -> Const
maxConst = maybe Type (un Max) <<< foldMap (Just <<< Max)

{-| Function that converts the value inside an `Embed` constructor into a new
    expression
-}
type Typer m a = a -> Expr m a

confirm :: forall w r m a x y. x -> Feedback w r m a y -> Feedback w r m a x
confirm a = (<<<) wrap $ unwrap >>> case _ of
  V.Success (Tuple _ accum) ->
    V.Success (Tuple a accum)
  V.Error es mtaccum ->
    V.Error es $ pure $ Tuple a $ foldMap extract mtaccum

mconfirm :: forall w r m a x. Maybe x -> Feedback w r m a x -> Feedback w r m a x
mconfirm = case _ of
  Nothing -> identity
  Just a -> confirm a

newtype TypeCheckError r a = TypeCheckError
  -- The main location where the typechecking error occurred
  { location :: a
  -- The tag for the specific error, mostly for machine purposes
  , tag :: Variant r
  }
derive instance functorTypeCheckError :: Functor (TypeCheckError r)
derive newtype instance showTypeCheckError :: (Show a, Show (Variant r)) => Show (TypeCheckError r a)

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
--   Left left (Lazy): alphaNormalize
--   Left right left (Bicontext): current context
--   Left right right (Lazy): substitution+normalization (idempotent, but this isn't enforced ...)
--   Right (Lazy Feedback): typechecking
-- TODO: more operations? extensibility? connect to GenericExprAlgebra?
type Operations w r m a = Product (Product Lazy (WithBiCtx Lazy)) (Compose Lazy (Feedback w r m a))
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
typecheckSketch :: forall w r m a. Eq a => MapLike String m =>
  (WithBiCtx (LxprF m a) (Oxpr w r m a) -> Feedback w r m a (Lxpr m a)) ->
  Lxpr m a -> Ocpr w r m a
typecheckSketch alg = recursor2D
  \layer@(EnvT (Tuple loc e)) -> ReaderT \ctx -> Product $ Tuple
      do Product $ Tuple
          do
            defer \_ ->
              alphaNormalizeLxpr $
              embed $ EnvT $ Tuple loc $ head2D <$> e
          -- FIXME: is context empty after normalization? idk
          do WithBiCtx (ctx <#> join bimap head2D) $ -- FIXME: memoization lost
              defer \_ ->
                -- Normalize (and substitute!) the context before substitution
                let ctx' = ctx <#> theseLeft >>> map (normalizeStep >>> head2D)
                    --unused = unsafePerformEffect $ log $ unsafeCoerce $ Array.fromFoldable $ map fst $ unwrap $ ctx
                in
                normalizeLxpr $
                substContextLxpr ctx' $
                embed $ EnvT $ Tuple loc $ head2D <$> e
      do Compose $ defer \_ ->
          map (alsoOriginateFrom (Loc.stepF (_S::S_ "typecheck") <$> loc)) $
          alg $ WithBiCtx ctx $ (((layer))) #
            -- contextualize each child of `layer` in the proper context,
            -- adapted for its place in the AST
            -- (in particular, if `layer` is `Let`/`Pi`/`Lam`)
            do mapEnvT $ _Newtype $ bicontextualizeWithin1 shiftInOxpr0 bicontextualizeWithin ctx

-- Run the alpha-normalization operation.
alphaNormalizeOp :: forall w r m a b. Operations w r m a b -> b
alphaNormalizeOp (Product (Tuple (Product (Tuple lz _)) _)) = extract lz

-- Get the context
contextOp :: forall w r m a b. Operations w r m a b -> BiContext b
contextOp (Product (Tuple (Product (Tuple _ (WithBiCtx ctx _))) _)) = ctx

-- Run the normalization operation.
normalizeOp :: forall w r m a b. Operations w r m a b -> b
normalizeOp (Product (Tuple (Product (Tuple _ (WithBiCtx _ lz))) _)) = extract lz

-- Run the typechecking operation.
typecheckOp :: forall w r m a. Operations w r m a ~> Feedback w r m a
typecheckOp (Product (Tuple _ (Compose lz))) = extract lz

-- Alphanormalize an Oxpr (once).
alphaNormalizeStep :: forall w r m a.
  Oxpr w r m a -> Oxpr w r m a
alphaNormalizeStep = step2D >>> alphaNormalizeOp

-- Get the context associated with the Oxpr node
contextStep :: forall w r m a.
  Oxpr w r m a -> BiContext (Oxpr w r m a)
contextStep = step2D >>> contextOp

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
    # mapWithIndex \i' -> (#) $ Loc.moveF (_S::S_ "within") i' <$> loc

-- Same drill, but for a tree that already has locations.
alsoOriginateFrom :: forall m a. FunctorWithIndex String m =>
  L m a -> Lxpr m a -> Lxpr m a
alsoOriginateFrom = flip <<< cata <<< flip $ go where
  go loc (EnvT (Tuple f e)) = embed $ EnvT $ Tuple (loc <> f) $ (((e)))
    # mapWithIndex \i' -> (#) $ Loc.moveF (_S::S_ "within") i' <$> loc

topLoc :: forall w r m a. Oxpr w r m a -> L m a
topLoc = project >>> un Compose >>> extract >>> env

alsoOriginateFromO :: forall w r m a. FunctorWithIndex String m =>
  L m a -> Oxpr w r m a -> Oxpr w r m a
alsoOriginateFromO = mapR <<< over Compose <<< go where
  go loc e =
    Cofree.deferCofree \_ -> Tuple (Cofree.head e) (Cofree.tail e)
    # bimap
      do mapEnv (loc <> _) >>> mapEnvT (mapWithIndex \i' -> mapR $ over Compose $ go $ Loc.moveF (_S::S_ "within") i' <$> loc)
      do bitransProduct (map (go (Loc.stepF (_S::S_ "normalize") <$> loc))) (map (go (Loc.stepF (_S::S_ "typecheck") <$> loc)))

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
  DoNothing -> go ctx
  Clear -> go Dhall.Context.empty
  Intro (Tuple name introed) -> go $
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
  DoNothing -> go ctx
  Clear -> go Dhall.Context.empty
  Intro (Tuple name introed) -> go $
    Dhall.Context.insert name (map (shiftIn_node' name <<< go ctx) $ theseLeft introed) $
      map (shiftIn_node' name) <$> ctx

-- Insert an empty entry instead
-- Conservative substitution: let bindings within the selection are not
-- substituted, but bindings from outside are brought in
substcontextualizeWithin10 :: forall m a node node'.
  (String -> node' -> node') -> -- shift in a name
  (SubstContext node' -> node -> node') ->
  SubstContext node' ->
  AST.ExprLayerF m a node ->
  AST.ExprLayerF m a node'
substcontextualizeWithin10 shiftIn_node' go ctx = trackIntro case _ of
  DoNothing -> go ctx
  Clear -> go Dhall.Context.empty
  Intro (Tuple name introed) -> go $
    Dhall.Context.insert name empty $
      map (shiftIn_node' name) <$> ctx

-- Substitute any variables available in the context (via `let` bindings),
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

-- Substitute a fixed context, not adding entries from `let` bindings
substContext10 :: forall m a node node'.
  (String -> node' -> node') -> -- shift in a name
  (SubstContext node' -> node -> node') ->
  SubstContext node' ->
  AST.ExprLayerF m a node ->
  Either node' (AST.ExprLayerF m a node')
substContext10 shiftIn_node' go ctx =
  substcontextualizeWithin10 shiftIn_node' go ctx >>>
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
substContextLxpr :: forall m a. FunctorWithIndex String m =>
  SubstContext (Lxpr m a) ->
  Lxpr m a -> Lxpr m a
substContextLxpr ctx e = alsoOriginateFrom (Loc.stepF (_S::S_ "substitute") <$> extract e) $
  (#) ctx $ (((e))) # cata \(EnvT (Tuple loc (ERVF layer))) ctx' ->
    case substContext1 shiftInLxpr0 (#) ctx' layer of
      Left e' -> e'
      Right layer' -> embed $ EnvT $ Tuple loc $ ERVF layer'

-- Also make sure the context has its items substituted
substContextLxprCtx :: forall m a. FunctorWithIndex String m =>
  SubstContext (Lxpr m a) ->
  Lxpr m a -> Lxpr m a
substContextLxprCtx ctx = substContextLxpr
  (reconstituteCtx (map <<< substContextLxpr) ctx)

substContextOxpr :: forall w r m a. FunctorWithIndex String m =>
  SubstContext (Oxpr w r m a) ->
  Oxpr w r m a -> Oxpr w r m a
substContextOxpr ctx e = alsoOriginateFromO (Loc.stepF (_S::S_ "substitute") <$> topLoc e) $
  (mapR $ over Compose $ go $ reconstituteCtx (map <<< substContextOxpr) ctx) e where
    go ctx' e' = Cofree.deferCofree \_ ->
      case go1 ctx' (Cofree.head e') of
        Left (In (Compose e'')) -> (Tuple <$> Cofree.head <*> Cofree.tail) e''
        Right layer' -> Tuple layer' $ go ctx' <$> Cofree.tail e'
    go1 ctx' (EnvT (Tuple loc (ERVF layer))) =
      case substContext1 shiftInOxpr0 (mapR <<< over Compose <<< go) ctx' layer of
        Left e' -> Left $ e'
        Right layer' -> Right $ EnvT $ Tuple loc $ ERVF layer'


substContextOxprCtx :: forall w r m a. FunctorWithIndex String m =>
  SubstContext (Oxpr w r m a) ->
  Oxpr w r m a -> Oxpr w r m a
substContextOxprCtx ctx = substContextOxpr
  (reconstituteCtx (map <<< substContextOxpr) ctx)

-- Substitute context all the way down an Expr.
substContextExpr :: forall m a.
  SubstContext (Expr m a) ->
  Expr m a -> Expr m a
substContextExpr = flip $ cata \(ERVF layer) ctx' ->
  case substContext1 (\name -> shift 1 (AST.V name 0)) (#) ctx' layer of
    Left e' -> e'
    Right layer' -> embed $ ERVF layer'

substContextExpr0 :: forall m a.
  SubstContext (Expr m a) ->
  Expr m a -> Expr m a
substContextExpr0 = flip $ cata \(ERVF layer) ctx' ->
  case substContext10 (\name -> shift 1 (AST.V name 0)) (#) ctx' layer of
    Left e' -> e'
    Right layer' -> embed $ ERVF layer'

substContextExprCtx :: forall m a.
  SubstContext (Expr m a) ->
  Expr m a -> Expr m a
substContextExprCtx ctx = substContextExpr
  (reconstituteCtx (map <<< substContextExpr) ctx)

substContextExpr0Ctx :: forall m a.
  SubstContext (Expr m a) ->
  Expr m a -> Expr m a
substContextExpr0Ctx ctx = substContextExpr0
  (reconstituteCtx (map <<< substContextExpr0) ctx)

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
    # mapWithIndex \i -> alsoOriginateFrom (pure (Loc.moveF (_S::S_ "within") i (Tuple empty (Just e_))))

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

alphaNormalizeLxpr :: forall m a. FunctorWithIndex String m => Lxpr m a -> Lxpr m a
alphaNormalizeLxpr e = alsoOriginateFrom (Loc.moveF (_S::S_ "alphaNormalize") {} <$> extract e) $
  (((e))) #
    runLxprAlg (Variant.case_ # alphaNormalizeAlgG)
      (Variant.inj (_S::S_ "alphaNormalize") { ctx: Dhall.Context.empty })

shiftLxpr :: forall m a. FunctorWithIndex String m =>
  Int -> Var -> Lxpr m a -> Lxpr m a
shiftLxpr delta variable e = alsoOriginateFrom (Loc.moveF (_S::S_ "shift") { delta, variable } <$> extract e) $
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

normalizeLxpr :: forall m a. MapLike String m => Eq a => Lxpr m a -> Lxpr m a
normalizeLxpr e = alsoOriginateFrom (Loc.stepF (_S::S_ "normalize") <$> extract e) $
  (extract <<< extract <<< unwrap) $
    -- TODO: use substLxpr and shiftLxpr here
    runLxprAlgM (Variant.case_ # Dhall.Normalize.normalizeWithAlgGW mempty)
      (Variant.inj (_S::S_ "normalize") mempty) e

areEq :: forall w r m a. Eq a => MapLike String m => Oxpr w r m a -> Oxpr w r m a -> Boolean
areEq ty0 ty1 =
  -- TODO: make sure ty0 and ty1 typecheck before normalizing them?
  let
    Pair ty0' ty1' = Pair ty0 ty1 <#>
      normalizeStep >>> plain >>> AST.unordered >>> alphaNormalize
  in ty0' == ty1'

locateO' :: forall w r m a. Eq a => MapLike String m =>
  OxprE w ( "Not found" :: ExprRowVFI | r ) m a ->
  Variant (Operated + Derived + Within + ()) ->
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
  , within: \i -> V.liftW $
      foc0 # unlayerO # ERVF # preview (_ix i) # do
        V.note $ TypeCheckError
          { location: topLoc foc0
          , tag: Variant.inj (_S::S_ "Not found") i
          }
  }

locateO :: forall w r m a. Eq a => MapLike String m =>
  OxprE w ( "Not found" :: ExprRowVFI | r ) m a ->
  Derivation ->
  FeedbackE w ( "Not found" :: ExprRowVFI | r ) m a
    (OxprE w ( "Not found" :: ExprRowVFI | r ) m a)
locateO foc0 deriv = foldr (\v foc -> foc >>= flip locateO' v) (pure foc0) deriv

locateE' :: forall w r m a. Eq a => MapLike String m =>
  (a -> Expr m a) ->
  Variant (Operated + Derived + Within + ()) ->
  Tuple (BiContext (Expr m a)) (Expr m a) ->
  FeedbackE w ( "Not found" :: ExprRowVFI | r ) m a
    (Tuple (BiContext (Expr m a)) (Expr m a))
locateE' tpa = Variant.match
  let
    substCtx = extend \(Tuple ctx e) -> substContextExpr0 (theseLeft <$> ctx) e
    typecheck (Tuple ctx e) = do
      ctx' <- ctx # reconstituteCtxM \ctx' -> case _ of
        This val -> typeWithA tpa ctx' val
        That ty -> pure ty
        Both _ ty -> pure ty
      Tuple ctx <$> typeWithA tpa ctx' e
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
  , within: \i -> \(Tuple ctx e) -> V.liftW $
      let
        intro = Tuple <<< case _ of
          DoNothing -> ctx
          Clear -> Dhall.Context.empty
          Intro (Tuple k th) -> join bimap (Variables.shift 1 (V k 0)) <$>
            Dhall.Context.insert k th ctx
      in e # project # un ERVF # trackIntro intro # ERVF # preview (_ix i) # do
        V.note $ TypeCheckError
          { location: pure (Tuple empty empty)
          , tag: Variant.inj (_S::S_ "Not found") i
          }
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

newtype Inconsistency a = Inconsistency (NonEmpty (NonEmpty List) a)
derive instance newtypeInconsistency :: Newtype (Inconsistency a) _
derive newtype instance showInconsistency :: Show a => Show (Inconsistency a)
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
    List.Nil -> accum
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

ensureConsistency :: forall m f v. Applicative f => MapLike String m =>
  (v -> v -> Boolean) ->
  (Inconsistency (NonEmptyList { key :: String, value :: v }) -> f Void) ->
  m v -> f Unit
ensureConsistency egal error = traverse_ error
  <<< consistency
  <<< tabulateGroupings egal
  <<< map (uncurry { key: _, value: _ })
  <<< Dhall.Map.toUnfoldable

data WithHint f a = WithHint (Maybe a) (f a)
derive instance functorWithHint :: Functor f => Functor (WithHint f)
instance functorWithIndexWithHint :: FunctorWithIndex i f => FunctorWithIndex (Maybe i) (WithHint f) where
  mapWithIndex f (WithHint ma fa) = WithHint (f Nothing <$> ma) (mapWithIndex (f <<< Just) fa)
instance foldableWithHint :: Foldable f => Foldable (WithHint f) where
  foldMap f (WithHint ma fa) = foldMap f ma <> foldMap f fa
  foldl f = foldlDefault f
  foldr f = foldrDefault f

ensureConsistentOxpr ::
  forall i c f w r m a.
    Applicative f => MapLike String m =>
    FunctorWithIndex i c => Foldable c => Eq a =>
  (Unit -> f Void) ->
  (Inconsistency (NonEmptyList { key :: i, value :: L m a }) -> f Void) ->
  c (Oxpr w r m a) -> f (Oxpr w r m a)
ensureConsistentOxpr missing error = finalize
  <<< tabulateGroupings areEq
  <<< List.fromFoldable
  <<< mapWithIndex { key: _, value: _ } where
    finalize :: List (NonEmptyList { key :: i, value :: Oxpr w r m a }) -> f (Oxpr w r m a)
    finalize List.Nil = absurd <$> missing unit
    finalize (List.Cons (NonEmptyList (a :| List.Nil)) List.Nil) = pure a.value
    finalize (List.Cons (NonEmptyList (a :| List.Cons b bs)) List.Nil) =
      let ixs = foldMap1 (topLoc <<< _.value) (NonEmptyList (b :| bs))
      in pure $ alsoOriginateFromO ixs a.value
    finalize (List.Cons a0 (List.Cons a1 an)) =
      map absurd $ error $ (map <<< map <<< prop (_S::S_ "value")) topLoc $
        Inconsistency $ a0 :| a1 :| an


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
  , "If branch must be term" :: Tuple Boolean (Maybe Const)
  , "Invalid list type" :: Maybe Const
  , "Missing list type" :: Unit
  , "Invalid list element" :: Int
  , "Mismatched list elements" :: Int
  , "Cannot append non-list" :: Boolean
  , "Cannot interpolate" :: Natural
  , "List append mismatch" :: Unit
  , "List annotation must be list type" :: Unit
  , "Invalid `Some`" :: Maybe Const
  , "Duplicate record fields" :: NonEmptyList String
  , "Invalid field type" :: String
  , "Duplicate union alternatives" :: NonEmptyList String
  , "Invalid alternative type" :: String
  , "Inconsistent alternative types" :: Inconsistency (NonEmptyList String)
  , "Must combine a record" :: Tuple (List String) Boolean
  , "Must merge a record" :: Unit
  , "Must merge a union" :: Unit
  , "Missing merge type" :: Unit
  , "Missing handler" :: Set Unit
  , "Unused handlers" :: Set Unit
  , "Handler not a function" :: String
  , "Dependent handler function" :: String
  , "Handler input type mismatch" :: String
  , "Handler output type mismatch" :: Tuple (Maybe { key :: String, fn :: Boolean }) String
  , "Handler type mismatch" :: Tuple (Maybe { key :: String, fn :: Boolean }) String
  , "Cannot project" :: Unit
  , "Cannot project by expression" :: Unit
  , "Projection type mismatch" :: String
  , "Missing field" :: String
  , "Cannot access" :: Unit
  , "toMap takes a record" :: Unit
  , "Invalid toMap type annotation" :: Unit
  , "Invalid toMap type" :: Maybe Const
  , "Missing toMap type" :: Unit
  , "Inconsistent toMap types" :: Inconsistency (NonEmptyList (Maybe String))
  , "Wrong header type" :: Unit
  , "Invalid input type" :: Unit
  , "Invalid output type" :: Unit
  , "Unbound variable" :: Var
  , "Annotation mismatch" :: Unit
  , "Not an equivalence" :: Unit
  , "Assertion failed" :: Unit
  , "Incomparable expression" :: Boolean
  , "Equivalent type mismatch" :: Unit
  , "`Sort` has no type" :: Unit
  , "Unexpected type" :: Tuple Boolean SimpleExpr
  | r
  )
type FeedbackE w r m a = Feedback w (Errors r) m a
type OxprE w r m a = Oxpr w (Errors r) m a
type TypeCheckErrorE r a = TypeCheckError (Errors r) a

reconstituteCtx :: forall a b.
  (Context b -> a -> b) -> Context a -> Context b
reconstituteCtx f = (<<<) extract $ reconstituteCtxM $
  ((<<<) <<< (<<<)) Identity f

reconstituteCtxM :: forall a b m. Bind m => Applicative m =>
  (Context b -> a -> m b) -> Context a -> m (Context b)
reconstituteCtxM = reconstituteCtxFromM Dhall.Context.empty

-- TODO: MonadRec?
-- TODO: convince myself that no shifting needs to occur here
reconstituteCtxFromM :: forall a b m. Bind m => Applicative m =>
  Context b -> (Context b -> a -> m b) -> Context a -> m (Context b)
reconstituteCtxFromM ctx0 f = foldr f' (pure ctx0) <<< un Context <<< unshift where
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
  Eq a => MapLike String m =>
  Typer m a ->
  Context (Expr m a) ->
  Expr m a ->
  FeedbackE w r m a (Expr m a)
typeWithA tpa ctx0 e0 = map plain <<< typecheckStep =<< typingWithA tpa ctx0 e0

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
    -- (which must consist of Oxprs)
    tcingIn :: BiContext (OxprE w r m a) -> Expr m a -> FeedbackE w r m a (OxprE w r m a)
    tcingIn ctx e =
      let
        e' = tcingFrom (pure (Tuple empty (Just e))) e # bicontextualizeWithin ctx
      in e' <$ typecheckStep e'
  -- convert ctx0 and e0 to Oxprs
  ctxO <- reconstituteCtxM (\ctx ty -> That <$> tcingIn ctx ty) ctx0
  let eO = tcingFrom (pure (Tuple empty Nothing)) e0
  -- and run typechecking on eO
  pure $ bicontextualizeWithin ctxO eO

newtype NoStrMap a = NoStrMap (Const.Const Void a)
derive instance newtypeNoStrMap :: Newtype (NoStrMap a) _
derive newtype instance functorNoStrMap :: Functor NoStrMap
derive newtype instance foldableNoStrMap :: Foldable NoStrMap
derive newtype instance traversableNoStrMap :: Traversable NoStrMap
instance functorWithIndexNoStrMap :: FunctorWithIndex i NoStrMap where
  mapWithIndex _ (NoStrMap void) = absurd $ unwrap $ void
instance foldableableWithIndexNoStrMap :: FoldableWithIndex i NoStrMap where
  foldMapWithIndex _ (NoStrMap void) = absurd $ unwrap $ void
  foldlWithIndex _ _ (NoStrMap void) = absurd $ unwrap $ void
  foldrWithIndex _ _ (NoStrMap void) = absurd $ unwrap $ void
instance traversableWithIndexNoStrMap :: TraversableWithIndex i NoStrMap where
  traverseWithIndex _ (NoStrMap void) = absurd $ unwrap $ void
type SimpleExpr = Expr NoStrMap Void
rehydrate :: forall m a. Functor m => SimpleExpr -> Expr m a
rehydrate = map absurd <<< hoistExpr (absurd <<< unwrap <<< unwrap)

typecheckAlgebra :: forall w r m a. Eq a => MapLike String m =>
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
      when (not areEq ty0 ty1) $
        absurd <$> error unit
    checkEqL ::
      OxprE w r m a -> OxprE w r m a ->
      (Unit -> FeedbackE w r m a Void) ->
      FeedbackE w r m a (OxprE w r m a)
    checkEqL ty0 ty1 error = confirm ty0 $ checkEq ty0 ty1 error
    checkEqR ::
      OxprE w r m a -> OxprE w r m a ->
      (Unit -> FeedbackE w r m a Void) ->
      FeedbackE w r m a (OxprE w r m a)
    checkEqR ty0 ty1 error = confirm ty1 $ checkEq ty0 ty1 error

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
      SimpleExpr ->
      Pair (OxprE w r m a) ->
      FeedbackE w r m a (Lxpr m a)
    checkBinOp t p = confirm (newborn (rehydrate t)) $ forWithIndex_ p $
      -- t should be simple enough that alphaNormalize is unnecessary
      \side operand -> typecheckStep operand >>= normalizeStep >>> case _ of
        ty_operand | rehydrate t == plain ty_operand -> pure unit
          | otherwise -> errorHere
            (_S::S_ "Unexpected type") (Tuple side t)

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
        AST.mkPi "just" (AST.mkArrow a optional) $
          AST.mkPi "nothing" optional $
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
      (Maybe Const -> FeedbackE w r m a Void) ->
      FeedbackE w r m a (OxprE w r m a)
    ensureTerm expr error = do
      ty <- typecheckStep expr
      ty <$ ensureType ty error

    -- Ensure that the passed `ty` is a type; i.e. its type is `Type`.
    ensureType ::
      OxprE w r m a ->
      (Maybe Const -> FeedbackE w r m a Void) ->
      FeedbackE w r m a Unit
    ensureType ty error = do
      kind <- typecheckStep ty
      ensure' (_S::S_ "Const") kind (\_ -> error Nothing) >>= case _ of
        Const.Const Type -> pure unit
        Const.Const c -> absurd <$> error (Just c)
  in
  { "Const": unwrap >>> \c ->
      axiom c <#> newborn <<< AST.mkConst #
        noteHere (_S::S_ "`Sort` has no type") unit
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
      kI <- ensureConst ty
        (errorHere (_S::S_ "Invalid input type"))
      ty_body <- typecheckStep body
      kO <- ensureConst ty_body
        (errorHere (_S::S_ "Invalid output type"))
      pure $ mk(_S::S_"Pi") (AST.BindingBody name (head2D ty) (head2D ty_body))
  , "Pi": \(AST.BindingBody name ty ty_body) -> do
      kI <- ensureConst ty
        (errorHere (_S::S_ "Invalid input type"))
      kO <- ensureConst ty_body
        (errorHere (_S::S_ "Invalid output type"))
      map (newborn <<< AST.mkConst) $ rule kI kO
  , "Let": \(AST.LetF name mty value expr) -> do
      ty0 <- typecheckStep value
      ty <- fromMaybe ty0 <$> for mty \ty' -> do
        _ <- typecheckStep ty'
        checkEqR ty0 ty'
          (errorHere (_S::S_ "Annotation mismatch"))
      ty_expr <- typecheckStep expr
      let shifted = tryShiftOut0Lxpr name (head2D ty_expr)
      pure case shifted of
        Nothing -> mk(_S::S_"Let") (head2D <$> AST.LetF name mty value ty_expr)
        Just ty_expr' -> ty_expr'
  , "App": \(AST.Pair f a) ->
      let
        checkFn = ensure (_S::S_ "Pi") f
          (errorHere (_S::S_ "Not a function"))
        checkArg (AST.BindingBody name aty0 rty) aty1 =
          let shifted = tryShiftOut0Lxpr name (head2D rty) in
          if areEq aty0 aty1
            then pure case shifted of
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
              errorHere (_S::S_ "Type mismatch") unit # case shifted of
                Nothing -> identity
                Just rty' -> confirm rty'
      in join $ checkArg <$> checkFn <*> typecheckStep a
  , "Annot": \(AST.Pair expr ty) ->
      map head2D $ join $ checkEqR
        <$> typecheckStep expr
        <@> ty
        <@> errorHere (_S::S_ "Annotation mismatch")
        <* do
          ty # unlayerO # VariantF.on (_S::S_ "Const")
            (\_ -> pure unit)
            (\_ -> void $ typecheckStep ty)
  , "Equivalent": \p -> do
      Pair lty rty <- p # traverseWithIndex \i t ->
        ensureTerm t
          (errorHere (_S::S_ "Incomparable expression") <<< const i)
      _ <- checkEqR lty rty
        (errorHere (_S::S_ "Equivalent type mismatch"))
      pure $ newborn AST.mkType
  , "Assert": \(Identity equiv) -> do
      Pair l r <- ensure' (_S::S_ "Equivalent") equiv
        (errorHere (_S::S_ "Not an equivalence"))
      _ <- checkEqR l r
        (errorHere (_S::S_ "Assertion failed"))
      pure $ head2D equiv
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
            (errorHere (_S::S_ "If branch must be term") <<< Tuple false)
          <*> ensureTerm f
            (errorHere (_S::S_ "If branch must be term") <<< Tuple true)
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
  , "NaturalSubtract": always $ AST.mkArrow AST.mkNatural $ AST.mkArrow AST.mkNatural AST.mkNatural
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
  , "TextLit": \things -> confirm (newborn AST.mkText) $
      forWithIndex_ things \i expr -> ensure (_S::S_ "Text") expr
        (errorHere (_S::S_ "Cannot interpolate") <<< const i)
  , "TextAppend": checkBinOp AST.mkText
  , "TextShow": always $ AST.mkArrow AST.mkText AST.mkText
  , "List": identity aFunctor
  , "ListLit": \(Product (Tuple mty lit)) -> mconfirm (head2D <$> mty) do
      -- get the assumed type of the list
      (ty :: OxprE w r m a) <- case mty of
        -- either from annotation
        Just listty -> do
          let error = errorHere (_S::S_ "List annotation must be list type")
          AST.Pair list ty <- ensure' (_S::S_ "App") listty error
          normalizeStep list # unlayerO #
            VariantF.on (_S::S_ "List") (const (pure unit))
              \_ -> absurd <$> error unit
          confirm ty $ ensureType ty
            (errorHere (_S::S_ "Invalid list type"))
        -- or from the first element
        Nothing -> case Array.head lit of
          Nothing -> errorHere (_S::S_ "Missing list type") $ unit
          Just item -> do
            ensureTerm item
              (errorHere (_S::S_ "Invalid list type"))
      confirm (mkFunctor AST.mkList (head2D ty)) $ forWithIndex_ lit \i item -> do
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
          AST.mkApp AST.mkList $ AST.mkRecord $ Dhall.Map.fromFoldable
            [Tuple "index" AST.mkNatural, Tuple "value" a0]
  , "ListReverse": always $
      AST.mkForall "a" $ join AST.mkArrow
        (AST.mkApp AST.mkList a0)
  , "Optional": identity aFunctor
  , "None": always $
      AST.mkPi "A" AST.mkType $
        AST.mkApp AST.mkOptional (AST.mkVar (AST.V "A" 0))
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
          unwrap <$> ensure (_S::S_ "Const") ty
            (errorHere (_S::S_ "Invalid field type") <<< const field)
        pure $ newborn $ AST.mkConst $ maxConst kts'
  , "RecordLit": \kvs ->
      ensureNodupes
        (errorHere (_S::S_ "Duplicate record fields")) kvs
      *> do
        kts <- traverse typecheckStep kvs
        confirm (mk(_S::S_"Record") (head2D <$> kts)) do
          forWithIndex_ kts \field ty -> do
            ensure (_S::S_ "Const") ty
              (errorHere (_S::S_ "Invalid field type") <<< const field)
  , "Union": \kts ->
      ensureNodupes
        (errorHere (_S::S_ "Duplicate union alternatives") <<< map fst) kts
      *> do
        kts' <- forWithIndex kts \(Tuple field (_ :: Unit)) ty -> do
          unwrap <$> ensure (_S::S_ "Const") ty
            (errorHere (_S::S_ "Invalid field type") <<< const field)
        ensureConsistency (((<<<)<<<(<<<)) (fromMaybe true) $ lift2 eq)
          (errorHere (_S::S_ "Inconsistent alternative types") <<< (map <<< map) _.key) (unwrap kts')
        pure $ newborn $ AST.mkConst $ maxConst kts'
  , "Combine":
      let
        combineTypes here (p :: Pair (OxprE w r m a)) = do
          AST.Pair { const: constL, kts: ktsL } { const: constR, kts: ktsR } <-
            forWithIndex p \side ty -> do
              kts <- ensure' (_S::S_ "Record") ty
                (errorHere (_S::S_ "Must combine a record") <<< const (Tuple here side))
              const <- ensure (_S::S_ "Const") ty
                (errorHere (_S::S_ "Must combine a record") <<< const (Tuple here side))
              pure { kts, const }
          let combined = Dhall.Map.unionWith (pure pure) ktsL ktsR
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
              const <- ensureConst ty
                (errorHere (_S::S_ "Must combine a record") <<< const (Tuple here side))
              pure { kts, const }
          let combined = Dhall.Map.unionWith (pure pure) ktsL ktsR
          kts <- forWithIndex combined \k ->
            case _ of
              Both ktsL' ktsR' ->
                _.rec <$> combineTypes (k : here) (AST.Pair ktsL' ktsR')
              This t -> pure (head2D t)
              That t -> pure (head2D t)
          pure { const: max constL constR, rec: mk(_S::S_"Record") kts }
      in map (newborn <<< AST.mkConst <<< _.const) <<< combineTypes Nil
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
      let
        preference = Just <<< case _ of
          This a -> a
          That b -> b
          Both a _ -> a
      pure $ mk(_S::S_"Record") $ map head2D $ Dhall.Map.unionWith (pure preference) ktsR ktsL
  , "Merge": \(AST.MergeF handlers cases mty) -> do
      Tuple ktsX (Compose ktsY) <- Tuple
        <$> ensure (_S::S_ "Record") handlers
          (errorHere (_S::S_ "Must merge a record"))
        <*> ensure (_S::S_ "Union") cases
          (errorHere (_S::S_ "Must merge a union"))
      let
        ksX = Set.fromFoldable $ ktsX $> unit
        ksY = Set.fromFoldable $ ktsY $> unit
        diffX = Set.difference ksX ksY
        diffY = Set.difference ksY ksX
      -- get the assumed type of the merge result
      Tuple whence ty <- case mty of
        -- either from annotation
        Just ty -> Tuple Nothing <$> pure ty
        -- or from the first handler
        Nothing -> case un First $ foldMapWithIndex (curry pure) ktsX of
          Nothing -> errorHere (_S::S_ "Missing merge type") $ unit
          Just (Tuple k item) -> do
            mtY <- Dhall.Map.get k ktsY #
              noteHere (_S::S_ "Unused handlers") diffX
            case mtY of
              Just _ -> do
                AST.BindingBody name _ output <- ensure' (_S::S_ "Pi") item
                  (errorHere (_S::S_ "Handler not a function") <<< const k)
                output' <- tryShiftOut0Oxpr name output #
                  (noteHere (_S::S_ "Dependent handler function") <<< const k $ unit)
                pure $ Tuple (Just { key: k, fn: true }) output'
              Nothing -> do
                pure $ Tuple (Just { key: k, fn: false }) item
      confirm (head2D ty) ado
        when (not Set.isEmpty diffX)
          (errorHere (_S::S_ "Unused handlers") diffX)
        forWithIndex_ ktsY \k mtY -> do
          tX <- Dhall.Map.get k ktsX #
            noteHere (_S::S_ "Missing handler") diffY
          case mtY of
            Just tY -> do
              AST.BindingBody name input output <- ensure' (_S::S_ "Pi") tX
                (errorHere (_S::S_ "Handler not a function") <<< const k)
              ado
                checkEq tY input
                  (errorHere (_S::S_ "Handler input type mismatch") <<< const k)
                do
                  output' <- tryShiftOut0Oxpr name output #
                    (noteHere (_S::S_ "Dependent handler function") <<< const k $ unit)
                  checkEq ty output'
                    (errorHere (_S::S_ "Handler output type mismatch") <<< const (Tuple whence k))
              in unit
            Nothing ->
              checkEq ty tX
                (errorHere (_S::S_ "Handler type mismatch") <<< const (Tuple whence k))
        in unit
  , "ToMap": \(Product (Tuple (Identity expr) mty)) -> mconfirm (head2D <$> mty) do
      kts <- ensure (_S::S_ "Record") expr
        (errorHere (_S::S_ "toMap takes a record"))
      let
        mapType ty =
          mkFunctor AST.mkList $ mk(_S::S_ "Record") $ Dhall.Map.fromFoldable
            [ Tuple "mapKey" $ mk(_S::S_ "Text") (wrap unit)
            , Tuple "mapValue" ty
            ]
      tyA <- mty # traverse \listty -> do
        -- TODO: better errors
        let error = errorHere (_S::S_ "Invalid toMap type annotation")
        AST.Pair list rty <- ensure' (_S::S_ "App") listty error
        normalizeStep list # unlayerO #
          VariantF.on (_S::S_ "List") (const (pure unit))
            \_ -> absurd <$> error unit
        tyS <- ensure' (_S::S_ "Record") rty error
        when (Dhall.Map.size tyS /= 2) (void $ error unit)
        tyK <- Dhall.Map.get "mapKey" tyS
          # noteHere (_S::S_ "Invalid toMap type annotation") unit
        _ <- ensure' (_S::S_ "Text") tyK error
        ty <- Dhall.Map.get "mapValue" tyS
          # noteHere (_S::S_ "Invalid toMap type annotation") unit
        confirm ty $ ensureType ty (errorHere (_S::S_ "Invalid toMap type"))
      ty <- ensureConsistentOxpr
        (errorHere (_S::S_ "Missing toMap type"))
        (errorHere (_S::S_ "Inconsistent toMap types") <<< (map <<< map) _.key)
        (WithHint tyA kts)
      pure $ mapType $ head2D ty
  , "Field": \(Tuple field expr) -> do
      tyR <- typecheckStep expr
      let
        error _ = errorHere (_S::S_ "Cannot access") unit
        handleRecord kts = do
          case Dhall.Map.get field kts of
            Just ty -> pure (head2D ty)
            Nothing -> errorHere (_S::S_ "Missing field") $ field
        handleType kts = do
          case Dhall.Map.get field kts of
            Just (Just ty) -> pure $ mk(_S::S_"Pi") $ map head2D $ (AST.BindingBody field ty expr)
            Just Nothing -> pure $ head2D expr
            Nothing -> errorHere (_S::S_ "Missing field") $ field
        casing = (\_ -> error unit)
          # VariantF.on (_S::S_ "Record") handleRecord
          # VariantF.on (_S::S_ "Const") \(Const.Const c) ->
              expr # normalizeStep # unlayerO #
                VariantF.on (_S::S_ "Union") (unwrap >>> handleType) (\_ -> error unit)
      tyR # normalizeStep # unlayerO # casing
  , "Project": \(Product (Tuple (Identity expr) projs)) -> do
      kts <- ensure (_S::S_ "Record") expr
        (errorHere (_S::S_ "Cannot project"))
      ks <- case projs of
        Left (App ks) -> pure $ ks <#> \(_ :: Unit) -> Nothing
        Right fields -> do
          _ <- typecheckStep fields
          -- TODO: right error?
          ks <- ensure' (_S::S_ "Record") fields (errorHere (_S::S_ "Cannot project by expression"))
          ks # traverse \ty -> Just ty <$ typecheckStep ty
      mk(_S::S_"Record") <<< map head2D <$> forWithIndex ks \k mty -> do
        ty0 <- Dhall.Map.get k kts #
          (noteHere (_S::S_ "Missing field") k)
        mty # maybe (pure ty0) \ty1 ->
          checkEqR ty0 ty1 (errorHere (_S::S_ "Projection type mismatch") <<< const k)
  , "Hashed": \(Tuple _ e) -> head2D <$> typecheckStep e
  , "UsingHeaders": \(Pair l r) ->
      head2D <$> typecheckStep l <* do
        let error = errorHere (_S::S_ "Wrong header type")
        (ty :: OxprE w r m a) <- typecheckStep r
        AST.Pair list (ty' :: OxprE w r m a) <- ensure' (_S::S_ "App") ty error
        _ <- ensure' (_S::S_ "List") list error
        (rec :: m (OxprE w r m a)) <- ensure' (_S::S_ "Record") ty' error
        when (Dhall.Map.size rec /= 2) (void $ error unit)
        (mapKey :: OxprE w r m a) <- Dhall.Map.get "mapKey" rec # noteHere (_S::S_ "Wrong header type") unit
        (mapValue :: OxprE w r m a) <- Dhall.Map.get "mapValue" rec # noteHere (_S::S_ "Wrong header type") unit
        _ <- ensure' (_S::S_ "Text") mapKey error
        _ <- ensure' (_S::S_ "Text") mapValue error
        pure unit
  , "ImportAlt": \(Pair l r) ->
      -- FIXME???
      case unwrap $ head2D <$> typecheckStep l of
        succ@(V.Success _) -> wrap succ
        V.Error es ml ->
          case unwrap $ head2D <$> typecheckStep r of
            succ@(V.Success _) -> wrap succ
            V.Error es' mr -> wrap $ V.Error (es <> es') (ml <|> mr)
  , "Embed": map newborn <<< tpa <<< unwrap
  }

data Reference a
  = Text String
  | Br
  | Reference a
  | List (Array (Reference a))
  | Compare String a String a
  | Href String String
  -- | NodeType String
derive instance functorReference :: Functor Reference

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
    bicontextualizeWithin Dhall.Context.empty $
      typecheckSketch (typecheckAlgebra tpa) $
        originateFrom (pure (Tuple empty loc)) $
          ei
  oxpr = oxprFrom Nothing e0
  get (Tuple loc me) = flip locateO loc $ case me of
    Nothing -> oxpr
    Just e1 -> oxprFrom (Just e1) e1
  locate (NonEmptyList (a :| as)) =
    case get a of
      suc@(WriterT (V.Success _)) -> suc
      err@(WriterT (V.Error _ _)) ->
        case oneOfMap (V.hushW' <<< get) as of
          Nothing -> err
          Just r -> pure r
  explainNotFound :: forall b. String -> Array (Reference b)
  explainNotFound i =
    [ Text $ "Could not find location: " <> i ]
  explainHere (TypeCheckError { location, tag: tag0 }) =
    tag0 # Variant.on (_S::S_ "Not found" ) (explainNotFound <<< show) \tag ->
      let
        located = V.hushW' $ locate location
        addLocation :: Loc.BasedExprDerivation m a -> L m a
        addLocation (Tuple path (Just base)) = pure $ Tuple path (Just base)
        addLocation (Tuple path Nothing) = bimap (path <> _) identity <$> location
      in case located of
        Just el ->
          let
            ctx = join bimap (const unit) <$> contextStep el
            nodeType = unit <$ unlayerO el
          in explain ctx nodeType tag <#> map (V.hushW' <<< locate <<< addLocation)
        Nothing -> explainNotFound (show location)

-- The explanation, given as text interspersed with specific places to look at
-- (for the user to read)
explain ::
  forall r m a.
    MapLike String m =>
  BiContext Unit ->
  VariantF (AST.ExprLayerRow m a) Unit ->
  Variant (Errors r) ->
  Array (Reference (Loc.BasedExprDerivation m a))
explain ctx nodeType =
  let errorUnknownError = [ Text "Unexplained error" ]
      within ::
        forall sym v r'.
          IsSymbol sym =>
          R.Cons sym v r' AST.ExprLayerRowI =>
        SProxy sym -> v -> Endo (->) (Loc.BasedExprDerivation m a)
      within sym v = within' (ERVFI (Variant.inj sym v))
      within' :: ExprRowVFI -> Endo (->) (Loc.BasedExprDerivation m a)
      within' ervfi = Endo $ Loc.moveF (_S::S_ "within") ervfi
      typechecked :: Endo (->) (Loc.BasedExprDerivation m a)
      typechecked = Endo $ Loc.stepF (_S::S_ "typecheck")
      normalized :: Endo (->) (Loc.BasedExprDerivation m a)
      normalized = Endo $ Loc.stepF (_S::S_ "normalize")
      expr :: Expr m Void -> Loc.BasedExprDerivation m a
      expr e = Tuple empty $ pure $ absurd <$> e
      referenceExpr :: Expr m Void -> Reference (Loc.BasedExprDerivation m a)
      referenceExpr e = Reference (expr e)
      referenceConst :: AST.Const -> Reference (Loc.BasedExprDerivation m a)
      referenceConst = referenceExpr <<< AST.mkConst
      reference :: Endo (->) (Loc.BasedExprDerivation m a) -> Reference (Loc.BasedExprDerivation m a)
      reference = Reference <<< dereference
      dereference :: Endo (->) (Loc.BasedExprDerivation m a) -> Loc.BasedExprDerivation m a
      dereference (Endo localize) = localize (Tuple empty Nothing)
      compare :: String -> Endo (->) (Loc.BasedExprDerivation m a) -> String -> Endo (->) (Loc.BasedExprDerivation m a) -> Reference (Loc.BasedExprDerivation m a)
      compare s1 l1 s2 l2 = Compare s1 (dereference l1) s2 (dereference l2)
      here = reference mempty

      notAType desc loc =
        [ Text $ "The " <> (if String.null desc then "" else desc <> " ") <> " type "
        , reference loc
        , Text " is required to be a type in some universe, e.g. "
        , referenceExpr AST.mkType
        , Text " but instead had type "
        , reference (typechecked <> loc)
        ]
  in
  Variant.default errorUnknownError #
  Variant.onMatch
  { "`Sort` has no type": \(_ :: Unit) ->
    [ Text "Sort is the top universe of types and therefore it has no type itself" ]
  , "Not a function": \(_ :: Unit) ->
      [ Text $ "The left side of a function application node must be a function "
      , Text $ "(i.e. a term whose type is a Pi type)"
      , Text $ " but instead it had type "
      , reference $ typechecked <> within (_S::S_ "App") false
      ]
  , "Type mismatch": \(_ :: Unit) ->
      [ compare
          "The function takes values in type "
          (  within (_S::S_ "Pi") false
          <> normalized <> typechecked
          <> within (_S::S_ "App") false
          ) " but was instead given a value of type "
          (  normalized
          <> typechecked
          <> within (_S::S_ "App") true
          )
      ]
  , "Invalid predicate": \(_ :: Unit) ->
      [ Text $ "If-then-else expressions take predicates whose type is "
      , referenceExpr AST.mkBool
      , Text $ " but the predicate had this type instead "
      , reference $ typechecked <> within (_S::S_ "BoolIf") AST.Three1
      ]
  , "If branch mismatch": \(_ :: Unit) ->
      [ Text $ "If expressions must have the same type in the `then` branch as the `else` branch, "
      , compare
          " but the former was "
          (typechecked <> within (_S::S_ "BoolIf") AST.Three2)
          " and the latter was "
          (typechecked <> within (_S::S_ "BoolIf") AST.Three3)
      ]
  , "If branch must be term": \(Tuple side mc) ->
      let focus = within (_S::S_ "BoolIf") if side then AST.Three3 else AST.Three2 in
      [ Text $ "If-then-else expressions must return a term "
      , Text $ "(since dependent types are forbidden)"
      , Text $ " but the expression had type "
      , reference $ typechecked <> focus
      ] <> case mc of
        Nothing ->
          [ Text $ " which is not in a type universe, but instead had type "
          , reference $ typechecked <> typechecked <> focus
          ]
        Just c ->
          [ Compare
              " which was in universe "
              (expr (AST.mkConst c))
              " instead of "
              (expr (AST.mkConst AST.Type))
          ]
  -- TODO: needs work
  , "Invalid list type": \(mc :: Maybe Const) ->
      let
        annot = ERVFI (Variant.inj (_S::S_ "ListLit") (Left unit))
        focus = if has (_ix annot) (ERVF nodeType) then within' annot else
          typechecked <> within (_S::S_ "ListLit") (Right zero)
      in
      [ Text $ "A list should contain elements in the universe "
      , referenceExpr AST.mkType
      , Text $ " but this is not "
      , reference (typechecked <> focus)
      ]
  , "Missing list type": \(_ :: Unit) ->
      [ Text "Empty list literals must be annotated with the type of their elements" ]
  , "Invalid list element": \i ->
      [ Text $ "The list was annotated to have type "
      , reference $ within (_S::S_ "ListLit") (Left unit)
      , Text $ " but the element at index "
      , Text $ show i
      , Text $ " had type "
      , reference $ typechecked <> within (_S::S_ "ListLit") (Right i)
      ]
  -- TODO: needs work
  , "Mismatched list elements": \i ->
      [ Text $ "The list was assumed to have type "
      , reference $ typechecked <> within (_S::S_ "ListLit") (Right zero)
      , Text $ " but the element at index "
      , Text $ show i
      , Text $ " had type "
      , reference $ typechecked <> within (_S::S_ "ListLit") (Right i)
      ]
  , "Cannot append non-list": \(side :: Boolean) ->
      let focus = within (_S::S_ "ListAppend") side in
      [ Text $ "Appending lists requires the operands to be lists"
      , Text $ " but the " <> (if side then "right" else "left") <> " side instead had type "
      , reference $ normalized <> typechecked <> focus
      ]
  , "Cannot interpolate": \(i :: Natural) ->
      let focus = within (_S::S_ "TextLit") i in
      [ Text $ "Expressions interpolated into a text literal must have type "
      , referenceExpr AST.mkText
      , Text $ " but this instead had type "
      , reference $ typechecked <> focus
      ]
  , "List append mismatch": \(_ :: Unit) ->
      let
        elType side =
          within (_S::S_ "App") true <>
          normalized <> typechecked <>
          within (_S::S_ "ListAppend") side
      in
      [ Text $ "Appending lists requires the operands to be lists of equal types"
      , Text $ " but the left side has elements of type "
      , reference $ elType false
      , Text $ " while the right has elements of type "
      , reference $ elType true
      ]
  , "List annotation must be list type": \(_ :: Unit) ->
      [ Text $ "Lists must be annotated with a type that starts with `List`, but this one was annotated with "
      , reference $ within (_S::S_ "ListLit") (Left unit)
      ]
  , "Invalid `Some`": \(mc :: Maybe Const) ->
      let focus = within (_S::S_ "Some") unit in
      [ Text $ "A optional literal must contain a term but Some was given an expression "
      , reference $ focus
      , Text $ " of type "
      , reference $ typechecked <> focus
      ] <> case mc of
        Nothing ->
          [ Text $ " which is not in a type universe, but instead had type "
          , reference $ typechecked <> typechecked <> focus
          ]
        Just c ->
          [ Compare
              " which was in universe "
              (expr (AST.mkConst c))
              " instead of "
              (expr (AST.mkConst AST.Type))
          ]
  , "Duplicate record fields": \(keys :: NonEmptyList String) ->
      [ Text $ "The following names of fields occurred more than once in a Record (type): "
      , List $ Text <$> Array.fromFoldable keys
      ]
  , "Invalid field type": \name ->
      let
        focus = nodeType # VariantF.on (_S::S_ "RecordLit")
          do \_ -> typechecked <> within (_S::S_ "RecordLit") name
          -- NOTE: assume it is a Record type, if it's not a RecordLit
          do \_ -> within (_S::S_ "Record") name
      in
      [ Text $ "Record field types must live in a universe, but "
      , Text $ "`" <> name <> "` "
      , reference $ focus
      , Text $ " instead had type "
      , reference $ typechecked <> focus
      ]
  -- TODO
  , "Inconsistent alternative types": \keys ->
      let
        focus name = within (_S::S_ "Union") (Tuple name unit)
      in
      [ Text $ "Union alternative types must all live in the same universe, but these did not "
      , List $ Text <<< show <$> Array.fromFoldable keys
      ]
  , "Duplicate union alternatives": \(keys :: NonEmptyList String) ->
      [ Text $ "The following names of alternatives occurred more than once in a Union (type): "
      , List $ Text <$> Array.fromFoldable keys
      ]
  , "Invalid alternative type": \name ->
      let
        focus = within (_S::S_ "Union") (Tuple name unit)
      in
      [ Text $ "Union alternative types must live in a universe, but "
      , Text $ "`" <> name <> "` "
      , reference $ focus
      , Text $ " instead had type "
      , reference $ typechecked <> focus
      ]
  -- TODO
  , "Must combine a record": \(Tuple path side) ->
      let
        focus name = within (_S::S_ "Union") (Tuple name unit)
      in
      [
      ]
  , "Must merge a record": \(_ :: Unit) ->
      [ Text $ "Using the `merge` operator requires a record as the first argument, but this had type "
      , reference $ normalized <> typechecked <> within (_S::S_ "Merge") AST.Three1
      ]
  , "Must merge a union": \(_ :: Unit) ->
      [ Text $ "Using the `merge` operator requires a union as the second argument, but this had type "
      , reference $ normalized <> typechecked <> within (_S::S_ "Merge") AST.Three1
      ]
  -- TODO
  , "Missing handler": \names ->
    [ Text $ "Handlers for the `merge` operator "
    , Text $ "`" <> show names <> "` "
    ]
  , "Unused handlers": \names ->
    [ Text $ "Handlers for the `merge` operator "
    , Text $ "`" <> show names <> "` "
    ]
  , "Handler not a function": \name ->
      [ Text $ "Handlers for the `merge` operator "
      , Text $ "`" <> name <> "` "
      ]
  , "Dependent handler function": \name ->
      [ Text $ "Handlers for the `merge` operator "
      , Text $ "`" <> name <> "` "
      ]
  , "Handler input type mismatch": \name ->
      [ Text $ "Handlers for the `merge` operator "
      , Text $ "`" <> name <> "` "
      ]
  , "Handler output type mismatch": \(Tuple fromAnnot name) ->
      let
        assumed = case fromAnnot of
          Nothing -> within (_S::S_ "Merge") AST.Three3
          Just { key, fn } ->
            (if fn then within (_S::S_ "Pi") true else mempty) <>
            within (_S::S_ "Record") key <>
            normalized <> typechecked <> within (_S::S_ "Merge") AST.Three1
      in
      [ Text $ "The handler for the `merge` operator "
      , Text $ "`" <> name <> "` "
      , compare
          " was expected to have type "
          assumed
          " but instead had type "
          (within (_S::S_ "Pi") true <> within (_S::S_ "Record") name <>
          normalized <> typechecked <> within (_S::S_ "Merge") AST.Three1)
      ]
  , "Handler type mismatch": \(Tuple fromAnnot name) ->
      let
        assumed = case fromAnnot of
          Nothing -> within (_S::S_ "Merge") AST.Three3
          Just { key, fn } ->
            (if fn then within (_S::S_ "Pi") true else mempty) <>
            within (_S::S_ "Record") key <>
            normalized <> typechecked <> within (_S::S_ "Merge") AST.Three1
      in
      [ Text $ "The handler for the `merge` operator case "
      , Text $ "`" <> name <> "` "
      , compare
          " was expected to have type "
          assumed
          " but instead had type "
          (within (_S::S_ "Record") name <>
          normalized <> typechecked <> within (_S::S_ "Merge") AST.Three1)
      ]
  , "Cannot project": \(_ :: Unit) ->
      [ Text $ "The projection operation can only be used on records, but the expression had type "
      , reference $ typechecked <> within (_S::S_ "Project") (Left unit)
      ]
  , "Cannot project by expression": \(_ :: Unit) ->
      [ Text $ "The project-by-expression operation can only take a record type, but this was not a record type "
      , reference $ normalized <> within (_S::S_ "Project") (Right unit)
      ]
  , "Projection type mismatch": \key ->
      [ Text $ "The field "
      , Text $ "`" <> key <> "`"
      , compare
          " should match its type in the  "
          (within (_S::S_ "Record") key <> normalized <> within (_S::S_ "Project") (Right unit))
          " but instead had type "
          (within (_S::S_ "Record") key <> normalized <> typechecked <> within (_S::S_ "Project") (Left unit))
      ]
  , "Missing field": \key ->
      let
        focus = nodeType # VariantF.on (_S::S_ "Field")
          do \_ -> within (_S::S_ "Field") unit
          do \_ -> within (_S::S_ "Project") (Left unit)
      in
      [ Text $ "The field "
      , Text $ "`" <> key <> "`"
      , Text $ " was missing from "
      , reference $ within (_S::S_ "Record") key <> normalized <> typechecked <> focus
      ]
  , "Cannot access": \(_ :: Unit) ->
      [ Text $ "The field accessor only works on records and union types, but this instead had type "
      , reference $ normalized <> typechecked <> within (_S::S_ "Field") unit
      ]
  , "toMap takes a record": \(_ :: Unit) ->
      [ Text $ "The `toMap` operation can only take a record, but this instead had type "
      , reference $ normalized <> typechecked <> within (_S::S_ "ToMap") (Left unit)
      ]
  , "Invalid toMap type annotation": \(_ :: Unit) ->
      [ Text $ "The `toMap` operation should have a type annotation that looks like "
      , referenceExpr $ AST.mkApp AST.mkList $ AST.mkRecord $ Dhall.Map.fromFoldable
        [ Tuple "mapKey" AST.mkText
        , Tuple "mapValue" (AST.mkVar (V "_" 0))
        ]
      , Text $ " but instead it was "
      , reference $ normalized <> within (_S::S_ "ToMap") (Right unit)
      ]
  -- TODO
  , "Invalid toMap type": \mc ->
      [ Text $ "The `toMap` operation should contain elements in the universe "
      , referenceExpr $ AST.mkType
      , Text $ " but instead the inferred type "
      ] <> case mc of
        Nothing ->
          [ Text $ " was not in a type universe"
          -- , but instead had type "
          -- , reference $ typechecked <> typechecked <> focus
          ]
        Just c ->
          [ Compare
              " which was in universe "
              (expr (AST.mkConst c))
              " instead of "
              (expr (AST.mkConst AST.Type))
          ]
  , "Missing toMap type": \(_ :: Unit) ->
      [ Text $ "The `toMap` operation, when its record is empty, must be annotated with a result type that looks like "
      , referenceExpr $ AST.mkApp AST.mkList $ AST.mkRecord $ Dhall.Map.fromFoldable
        [ Tuple "mapKey" AST.mkText
        , Tuple "mapValue" (AST.mkVar (V "_" 0))
        ]
      ]
  -- TODO
  , "Inconsistent toMap types": \keys ->
      [ Text $ "The `toMap` operation must have fields all of one type "
      , List $ Text <<< show <$> Array.fromFoldable keys
      ]
  , "Invalid input type": \(_ :: Unit) ->
      let
        ty = nodeType # VariantF.on (_S::S_ "Lam")
          do \_ -> within (_S::S_ "Lam") false
          -- NOTE: assume it is a Pi type, if it's not a Lam
          do \_ -> within (_S::S_ "Pi") false
      in
      notAType "input" ty
  , "Invalid output type": \(_ :: Unit) ->
      let
        ty_body = nodeType # VariantF.on (_S::S_ "Lam")
          do \_ -> typechecked <> within (_S::S_ "Lam") true
          -- NOTE: assume it is a Pi type, if it's not a Lam
          do \_ -> (within (_S::S_ "Pi") true)
      in
      notAType "output" ty_body
  , "Unbound variable": \(AST.V name idx) ->
      let
        scope =
          if null ctx then [ Text "The context was empty." ] else
          [ Text $ "The variables in scope, from most local to most global, are: "
          , List $ ctx # foldMapWithIndex \v' _ -> pure $
              referenceExpr $ AST.mkVar v'
          ]
      in (_ <> scope) $
      if not anyWithIndex (\(AST.V name' _) _ -> name == name') ctx
      then
      [ Text $ "There were no variables with name "
      , Text $ show name
      , Text $ " bound in scope. "
      ]
      else
      [ Text $ "The scope does not contain the variable "
      , Text $ show name
      , Text $ " at index "
      , Text $ show idx
      , Text $ ". "
      ]
  , "Annotation mismatch": \(_ :: Unit) ->
      let
        { value, ty } = nodeType # VariantF.on (_S::S_ "Let")
          do \_ ->
              { value: within (_S::S_ "Let") AST.Three2
              , ty: within (_S::S_ "Let") AST.Three1
              }
          -- NOTE: assume it is an Annot node, if not a Let
          do \_ ->
              { value: within (_S::S_ "Annot") false
              , ty: within (_S::S_ "Annot") true
              }
      in
      [ Text $ "The value "
      , reference value
      , compare
          " was annotated to have type "
          ty
          " but instead had type "
          (typechecked <> value)
      ]
  , "Unexpected type": \(Tuple side ty) ->
      ( if side
          then lastOf  (asIndex itraversed) (ERVF nodeType)
          else firstOf (asIndex itraversed) (ERVF nodeType)
      ) # foldMap \focus ->
      [ Text $ "The binary operator was expected to have operands of type "
      , referenceExpr $ rehydrate ty
      , Text $ " but instead its " <> (if side then "right" else "left") <> " operand had type "
      , reference $ typechecked <> within' focus
      ]
  , "Wrong header type": \(_ :: Unit) ->
      [ Compare
          "Headers are expected to have type "
          (expr headerType)
          " but this instead had type "
          (dereference $ typechecked <> within (_S::S_ "UsingHeaders") true)
      ]
  }

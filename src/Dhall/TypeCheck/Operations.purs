module Dhall.TypeCheck.Operations where

import Prelude

import Control.Comonad (class Comonad, extract)
import Control.Comonad.Cofree as Cofree
import Control.Comonad.Env (EnvT(..), mapEnvT)
import Control.Plus (empty)
import Data.Bifunctor (bimap)
import Data.Either (Either(..))
import Data.Foldable (class Foldable, foldr)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Mu (Mu(..))
import Data.Functor.Product (Product(..))
import Data.Functor.Variant as VariantF
import Data.FunctorWithIndex (class FunctorWithIndex, mapWithIndex)
import Data.Identity (Identity(..))
import Data.Lazy (defer)
import Data.Maybe (Maybe(..))
import Data.Monoid.Disj (Disj(..))
import Data.Newtype (over, un, unwrap, wrap)
import Data.Newtype as N
import Data.These (theseLeft)
import Data.Traversable (traverse)
import Data.TraversableWithIndex (class TraversableWithIndex)
import Data.Tuple (Tuple(..))
import Data.Variant as Variant
import Dhall.Context (Context(..))
import Dhall.Context as Dhall.Context
import Dhall.Core (Var, alphaNormalize, shift)
import Dhall.Core.AST (Expr, ExprRowVF(..), Pair(..), S_, _S)
import Dhall.Core.AST as AST
import Dhall.Core.AST.Operations.Location as Loc
import Dhall.Core.AST.Operations.Transformations (OverCases, OverCasesM(..))
import Dhall.Map (class MapLike)
import Dhall.Normalize as Dhall.Normalize
import Dhall.TypeCheck.Tree (bitransProduct, deshare, embedShared, env, head2D, mapEnv, recursor2DSharingCtx, shared, step2D, unEnvT, unshared, wasShared)
import Dhall.TypeCheck.Types (Ann, BiContext, Feedback, L, Lxpr, LxprF, Operations, Ospr, Oxpr, SubstContext, WithBiCtx(..), overBiCtx)
import Dhall.Variables (MaybeIntro(..), alphaNormalizeAlgG, freeInAlg, shiftAlgG, trackIntro)
import Matryoshka (class Recursive, cata, embed, mapR, project, transCata, traverseR)
import Unsafe.Reference (unsafeRefEq)

areEq :: forall w r m a. Eq a => MapLike String m => Oxpr w r m a -> Oxpr w r m a -> Boolean
areEq ty0 ty1 | unsafeRefEq ty0 ty1 = true -- perhaps there is enough sharing
areEq ty0 ty1 =
  let
    Pair ty0' ty1' = Pair ty0 ty1 <#>
      -- it appears that alphaNormalize is cheaper after `plain`,
      -- even though it is shared in `Oxpr`
      normalizeStep >>> plain >>> AST.unordered >>> alphaNormalize
  in ty0' == ty1'

-- Transforms the simple "typecheck one thing" algorithm to the full-blown
-- Lxpr -> Oxpr transformation (which includes typechecking and normalizing
-- each node inside the given context).
typecheckSketch :: forall w r m a. Eq a => MapLike String m =>
  (WithBiCtx (LxprF m a) (Oxpr w r m a) -> Feedback w r m a (Ospr w r m a)) ->
  Lxpr m a -> BiContext (Oxpr w r m a) -> Oxpr w r m a
typecheckSketch alg = unshared >>> recursor2DSharingCtx
  (\ctx -> mapEnvT $ over ERVF $ bicontextualizeWithin1 shiftInOxpr0 (#) ctx)
  \ctx (EnvT (Tuple loc layer)) ->
    -- contextualize each child of `layer` in the proper context,
    -- adapted for its place in the AST
    -- (in particular, if `layer` is `Let`/`Pi`/`Lam`)
    let
      layerShared = defer \_ ->
        embedShared $ EnvT $ Tuple loc $ shared <$> layer
    in Product $ Tuple
      do Product $ Tuple
          do
            defer \_ ->
              alphaNormalizeOspr $
              extract layerShared
          do WithBiCtx (ctx <#> join bimap shared) $
              Compose $ defer \_ ->
                -- Look ma! We get sharing for free!!
                let ctx' = ctx <#> theseLeft >>> map shared in
                normalizeOsprW $
                substContextOspr0 ctx' $
                extract layerShared
      do Compose $ defer \_ ->
          map (alsoOriginateFromS (Loc.stepF (_S::S_ "typecheck") <$> loc)) $
          alg $ WithBiCtx ctx $ EnvT (Tuple loc layer)

-- Run the alpha-normalization operation.
alphaNormalizeOp :: forall w r m a b. Operations w r m a b -> b
alphaNormalizeOp (Product (Tuple (Product (Tuple lz _)) _)) = extract lz

-- Get the context
contextOp :: forall w r m a b. Operations w r m a b -> BiContext b
contextOp (Product (Tuple (Product (Tuple _ (WithBiCtx ctx _))) _)) = ctx

-- Run the normalization operation.
normalizeOp :: forall w r m a b. Operations w r m a b -> b
normalizeOp = extract <<< extract <<< unwrap <<< normalizeOpW

normalizeOpW :: forall w r m a. Operations w r m a ~> Dhall.Normalize.W
normalizeOpW (Product (Tuple (Product (Tuple _ (WithBiCtx _ lz))) _)) =
  extract (unwrap lz)

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

normalizeStepW :: forall w r m a.
  Oxpr w r m a -> Dhall.Normalize.W (Oxpr w r m a)
normalizeStepW = step2D >>> normalizeOpW

-- Typecheck an Oxpr (once).
typecheckStep :: forall w r m a.
  Oxpr w r m a -> Feedback w r m a (Oxpr w r m a)
typecheckStep = step2D >>> typecheckOp

-- Unwrap the Expr layer at the top of an Oxpr.
unlayerO :: forall w r m a.
  Oxpr w r m a -> AST.ExprLayerF m a (Oxpr w r m a)
unlayerO = project >>> un Compose >>> extract >>> unEnvT >>> unwrap

-- Modify the Expr layer at the top of an Oxpr, and for all operations.
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
      do bitransProduct
          do bitransProduct
              do (map (go (Loc.stepF (_S::S_ "alphaNormalize") <$> loc)))
              do overBiCtx (map (go (Loc.stepF (_S::S_ "normalize") <$> loc)))
          do (map (go (Loc.stepF (_S::S_ "typecheck") <$> loc)))

alsoOriginateFromS :: forall w r m a. FunctorWithIndex String m =>
  L m a -> Ospr w r m a -> Ospr w r m a
alsoOriginateFromS = mapR <<< over Compose <<< go where
  go loc = bimap (alsoOriginateFromO loc)
    \(EnvT (Tuple f e)) -> EnvT $ Tuple (loc <> f) $ (((e)))
      # mapWithIndex \i' -> mapR $ over Compose $ go $ Loc.moveF (_S::S_ "within") i' <$> loc

topLocS :: forall w r m a. Ospr w r m a -> L m a
topLocS = project >>> un Compose >>> case _ of
  Left r -> topLoc r
  Right l -> env l

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

-- Substitute a context all the way down an Expr, snowballing as it goes
-- (i.e., `Let` bindings introduced in it are also substituted).
substContextExpr :: forall m a.
  SubstContext (Expr m a) ->
  Expr m a -> Expr m a
substContextExpr = flip $ cata \(ERVF layer) ctx' ->
  case substContext1 (\name -> shift 1 (AST.V name 0)) (#) ctx' layer of
    Left e' -> e'
    Right layer' -> embed $ ERVF layer'

-- Substitute an outer context everywhere inside an Expr, but do not substitute
-- inner `Let` bindnigs (i.e. no snowballing).
substContextExpr0 :: forall m a.
  SubstContext (Expr m a) ->
  Expr m a -> Expr m a
substContextExpr0 = flip $ cata \(ERVF layer) ctx' ->
  case substContext10 (\name -> shift 1 (AST.V name 0)) (#) ctx' layer of
    Left e' -> e'
    Right layer' -> embed $ ERVF layer'

-- Substitute, first making sure each item in context has been substituted,
-- with snowballing.
substContextExprCtx :: forall m a.
  SubstContext (Expr m a) ->
  Expr m a -> Expr m a
substContextExprCtx ctx = substContextExpr
  (reconstituteCtx (map <<< substContextExpr) ctx)

-- Substitute expression and context, no snowballing.
substContextExpr0Ctx :: forall m a.
  SubstContext (Expr m a) ->
  Expr m a -> Expr m a
substContextExpr0Ctx ctx = substContextExpr0
  (reconstituteCtx (map <<< substContextExpr0) ctx)

-- Substitute context all the way down an Lxpr.
substContextLxpr :: forall m a. FunctorWithIndex String m =>
  SubstContext (Lxpr m a) ->
  Lxpr m a -> Lxpr m a
substContextLxpr ctx e = alsoOriginateFrom (Loc.stepF (_S::S_ "substitute") <$> extract e) $
  (#) ctx $ (((e))) # cata \(EnvT (Tuple loc (ERVF layer))) ctx' ->
    case substContext1 shiftInLxpr0 (#) ctx' layer of
      Left e' -> e'
      Right layer' -> embed $ EnvT $ Tuple loc $ ERVF layer'

substContextLxprCtx :: forall m a. FunctorWithIndex String m =>
  SubstContext (Lxpr m a) ->
  Lxpr m a -> Lxpr m a
substContextLxprCtx ctx = substContextLxpr
  (reconstituteCtx (map <<< substContextLxpr) ctx)

substContextOxpr :: forall w r m a. FunctorWithIndex String m =>
  SubstContext (Oxpr w r m a) ->
  Oxpr w r m a -> Oxpr w r m a
substContextOxpr ctx e = alsoOriginateFromO (Loc.stepF (_S::S_ "substitute") <$> topLoc e) $
  (mapR $ over Compose $ go ctx) e where
    go ctx' e' = Cofree.deferCofree \_ ->
      case go1 ctx' (Cofree.head e') of
        Left (In (Compose e'')) -> (Tuple <$> Cofree.head <*> Cofree.tail) e''
        Right layer' -> Tuple layer' $ go ctx' <$> Cofree.tail e'
    go1 ctx' (EnvT (Tuple loc (ERVF layer))) =
      case substContext1 shiftInOxpr0 (mapR <<< over Compose <<< go) ctx' layer of
        Left e' -> Left e'
        Right layer' -> Right $ EnvT $ Tuple loc $ ERVF layer'

substContextOxpr0 :: forall w r m a. FunctorWithIndex String m =>
  SubstContext (Oxpr w r m a) ->
  Oxpr w r m a -> Oxpr w r m a
substContextOxpr0 ctx e = alsoOriginateFromO (Loc.stepF (_S::S_ "substitute") <$> topLoc e) $
  (mapR $ over Compose $ go ctx) e where
    go ctx' e' = Cofree.deferCofree \_ ->
      case go1 ctx' (Cofree.head e') of
        Left (In (Compose e'')) -> (Tuple <$> Cofree.head <*> Cofree.tail) e''
        Right layer' -> Tuple layer' $ go ctx' <$> Cofree.tail e'
    go1 ctx' (EnvT (Tuple loc (ERVF layer))) =
      case substContext10 shiftInOxpr0 (mapR <<< over Compose <<< go) ctx' layer of
        Left e' -> Left e'
        Right layer' -> Right $ EnvT $ Tuple loc $ ERVF layer'

substContextOxprCtx :: forall w r m a. FunctorWithIndex String m =>
  SubstContext (Oxpr w r m a) ->
  Oxpr w r m a -> Oxpr w r m a
substContextOxprCtx ctx = substContextOxpr
  (reconstituteCtx (map <<< substContextOxpr) ctx)

substContextOspr :: forall w r m a. FunctorWithIndex String m =>
  SubstContext (Ospr w r m a) ->
  Ospr w r m a -> Ospr w r m a
substContextOspr ctx e = alsoOriginateFromS (Loc.stepF (_S::S_ "substitute") <$> topLocS e) $
  (mapR $ over Compose $ go ctx) e where
    go :: SubstContext (Ospr w r m a) ->
      Either (Oxpr w r m a) (LxprF m a (Ospr w r m a)) ->
      Either (Oxpr w r m a) (LxprF m a (Ospr w r m a))
    go ctx' = case _ of
      -- Try to preserve sharing if all of ctx is shared
      Left r -> case (traverse <<< traverse) wasShared ctx' of
        Just ctx'' -> Left $ substContextOxpr ctx'' r
        Nothing -> go1 ctx' $ map shared $ Cofree.head $ un Compose $ project r
      Right layer -> go1 ctx' layer
    go1 :: SubstContext (Ospr w r m a) ->
      LxprF m a (Ospr w r m a) ->
      Either (Oxpr w r m a) (LxprF m a (Ospr w r m a))
    go1 ctx' (EnvT (Tuple loc (ERVF layer))) =
      case substContext1 shiftInOspr0 (mapR <<< over Compose <<< go) ctx' layer of
        Left e' -> un Compose $ project e'
        Right layer' -> Right $ EnvT $ Tuple loc $ ERVF layer'

substContextOspr0 :: forall w r m a. FunctorWithIndex String m =>
  SubstContext (Ospr w r m a) ->
  Ospr w r m a -> Ospr w r m a
substContextOspr0 ctx e = alsoOriginateFromS (Loc.stepF (_S::S_ "substitute") <$> topLocS e) $
  (mapR $ over Compose $ go ctx) e where
    go :: SubstContext (Ospr w r m a) ->
      Either (Oxpr w r m a) (LxprF m a (Ospr w r m a)) ->
      Either (Oxpr w r m a) (LxprF m a (Ospr w r m a))
    go ctx' = case _ of
      -- Try to preserve sharing if all of ctx is shared
      Left r -> case (traverse <<< traverse) wasShared ctx' of
        Just ctx'' -> Left $ substContextOxpr0 ctx'' r
        Nothing -> go1 ctx' $ map shared $ Cofree.head $ un Compose $ project r
      Right layer -> go1 ctx' layer
    go1 :: SubstContext (Ospr w r m a) ->
      LxprF m a (Ospr w r m a) ->
      Either (Oxpr w r m a) (LxprF m a (Ospr w r m a))
    go1 ctx' (EnvT (Tuple loc (ERVF layer))) =
      case substContext10 shiftInOspr0 (mapR <<< over Compose <<< go) ctx' layer of
        Left e' -> un Compose $ project e'
        Right layer' -> Right $ EnvT $ Tuple loc $ ERVF layer'

-- Originate from ... itself. Profound.
newborn :: forall m a. FunctorWithIndex String m =>
  Expr m a -> Lxpr m a
newborn e0 = e0 # originateFrom (pure (Tuple empty (Just e0)))

-- Wrap an Lxpr layer, preserving and augmenting the existing locations
-- from the new root.
newmother :: forall m a. FunctorWithIndex String m =>
  AST.ExprLayerF m a (Lxpr m a) -> Lxpr m a
newmother e0 =
  let e_ = AST.embedW $ e0 <#> denote
  in embed $ EnvT $ Tuple (pure (Tuple empty (Just e_))) $ wrap e0
    # mapWithIndex \i -> alsoOriginateFrom (pure (Loc.moveF (_S::S_ "within") i (Tuple empty (Just e_))))

-- Wrap an Ospr layer, preserving and augmenting the existing locations
-- from the new root.
newshared :: forall w r m a. FunctorWithIndex String m =>
  AST.ExprLayerF m a (Ospr w r m a) ->
  Ospr w r m a
newshared e0 =
  let e_ = AST.embedW $ e0 <#> deshare >>> denote
  in embedShared $ EnvT $ Tuple (pure (Tuple empty (Just e_))) $ wrap e0
    # mapWithIndex \i -> alsoOriginateFromS (pure (Loc.moveF (_S::S_ "within") i (Tuple empty (Just e_))))

denote :: forall m a s.
  Ann m a s -> Expr m a
denote = transCata unEnvT

-- e.g. Oxpr -> Expr
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
    , overlayer: OverCasesM $ traverseR <<< travEnvT <<< (\f -> map ERVF <<< f <<< unwrap)
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

runOsprAlg :: forall w r m a i. FunctorWithIndex String m =>
  (
    i ->
    { unlayer :: Ospr w r m a -> AST.ExprLayerF m a (Ospr w r m a)
    , overlayer :: OverCases (AST.ExprLayerRow m a) (Ospr w r m a)
    , recurse :: i -> Ospr w r m a -> Identity (Ospr w r m a)
    , layer :: AST.ExprLayerF m a (Ospr w r m a) -> Ospr w r m a
    } -> Ospr w r m a -> Identity (Ospr w r m a)
  ) ->
  i -> Ospr w r m a -> Ospr w r m a
runOsprAlg alg = go where
  go i e = un Identity $ alg i
    { unlayer: unlayerOS
    , overlayer: OverCasesM (map pure <<< overlayerOS <<< map extract)
    , recurse: map Identity <<< go
    , layer: newshared
    } e

runOsprAlgM :: forall f w r m a i. FunctorWithIndex String m => Functor f =>
  (
    i ->
    { unlayer :: Ospr w r m a -> AST.ExprLayerF m a (Ospr w r m a)
    , overlayer :: OverCasesM f (AST.ExprLayerRow m a) (Ospr w r m a)
    , recurse :: i -> Ospr w r m a -> f (Ospr w r m a)
    , layer :: AST.ExprLayerF m a (Ospr w r m a) -> Ospr w r m a
    } -> Ospr w r m a -> f (Ospr w r m a)
  ) ->
  i -> Ospr w r m a -> f (Ospr w r m a)
runOsprAlgM alg = go where
  go i e = alg i
    { unlayer: unlayerOS
    , overlayer: OverCasesM overlayerOSM
    , recurse: go
    , layer: newshared
    } e

unlayerOS :: forall w r m a.
  Ospr w r m a -> AST.ExprLayerF m a (Ospr w r m a)
unlayerOS = project >>> unwrap >>> case _ of
    Left r -> r # unlayerO >>> map shared
    Right ft -> ft # unEnvT >>> unwrap

overlayerOS :: forall w r m a.
  (AST.ExprLayerF m a (Ospr w r m a) -> AST.ExprLayerF m a (Ospr w r m a)) ->
  Ospr w r m a -> Ospr w r m a
overlayerOS f = project >>> unwrap >>> case _ of
    Left r -> case extract $ un Compose $ project $ r of
      EnvT (Tuple e (ERVF x)) ->
        embedShared $ EnvT $ Tuple e $ ERVF $
          f (shared <$> x)
    Right ft -> embedShared $ (mapEnvT <<< over ERVF) f ft

overlayerOSM :: forall f w r m a. Functor f =>
  (AST.ExprLayerF m a (Ospr w r m a) -> f (AST.ExprLayerF m a (Ospr w r m a))) ->
  Ospr w r m a -> f (Ospr w r m a)
overlayerOSM f = project >>> unwrap >>> case _ of
    Left r -> case extract $ un Compose $ project $ r of
      EnvT (Tuple e (ERVF x)) ->
        embedShared <<< EnvT <<< Tuple e <<< ERVF <$>
          f (shared <$> x)
    Right ft -> embedShared <$> (travEnvT <<< (\f -> map ERVF <<< f <<< unwrap)) f ft
  where
    travEnvT f' (EnvT (Tuple e x)) = EnvT <<< Tuple e <$> f' x

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

shiftOspr :: forall w r m a. FunctorWithIndex String m => Int -> Var -> Ospr w r m a -> Ospr w r m a
shiftOspr delta variable = runOsprAlg (Variant.case_ # shiftAlgG) $
  Variant.inj (_S::S_ "shift") { delta, variable }

shiftInOspr :: forall w r m a. FunctorWithIndex String m => Var -> Ospr w r m a -> Ospr w r m a
shiftInOspr = shiftOspr 1

shiftInOspr0 :: forall w r m a. FunctorWithIndex String m => String -> Ospr w r m a -> Ospr w r m a
shiftInOspr0 v = shiftInOspr (AST.V v 0)

shiftOutOspr :: forall w r m a. FunctorWithIndex String m => Var -> Ospr w r m a -> Ospr w r m a
shiftOutOspr = shiftOspr (-1)

alphaNormalizeOspr :: forall w r m a. MapLike String m => Eq a => Ospr w r m a -> Ospr w r m a
alphaNormalizeOspr e = alsoOriginateFromS (Loc.stepF (_S::S_ "alphaNormalize") <$> topLocS e) $
  let
    ops =
      { unlayer: unlayerOS
      , overlayer: OverCasesM overlayerOSM
      , recurse: \i -> go i
      }
    alg = Variant.case_ # alphaNormalizeAlgG
    go = Variant.match
      { alphaNormalize: \{ ctx } e' ->
          case un Compose (project e') of
            Left r | Dhall.Context.isEmpty ctx -> Identity (shared (alphaNormalizeStep r))
            _ -> alg (Variant.inj (_S::S_ "alphaNormalize") { ctx }) ops e'
      }
  in un Identity $ go (Variant.inj (_S::S_ "alphaNormalize") { ctx: Dhall.Context.empty }) e

normalizeOspr :: forall w r m a. MapLike String m => Eq a => Ospr w r m a -> Ospr w r m a
normalizeOspr = extract <<< normalizeOsprW

normalizeOsprW :: forall w r m a. MapLike String m => Eq a => Ospr w r m a -> Dhall.Normalize.W (Ospr w r m a)
normalizeOsprW e = alsoOriginateFromS (Loc.stepF (_S::S_ "normalize") <$> topLocS e) <$>
  let
    ops =
      { unlayer: unlayerOS
      , overlayer: OverCasesM overlayerOSM
      , recurse: \i -> go i
      , layer: newshared
      }
    alg = Variant.case_ # Dhall.Normalize.normalizeWithAlgGW mempty
    go = Variant.match
      { normalize: \_ e' ->
          case un Compose (project e') of
            Left r -> shared <$> normalizeStepW r
            _ -> alg (Variant.inj (_S::S_ "normalize") mempty) ops e'
      , shift: \{ delta, variable } -> pure <<< shiftOspr delta variable
      , subst: \i -> alg (Variant.inj (_S::S_ "subst") i) ops
      }
  in go (Variant.inj (_S::S_ "normalize") mempty) e

-- A helper: when applying an operation in a context, the context needs to be
-- initialized, step-by-step, just like the final result will be initialized
-- with that context.
reconstituteCtx :: forall a b.
  (Context b -> a -> b) -> Context a -> Context b
reconstituteCtx f = (<<<) extract $ reconstituteCtxM $
  ((<<<) <<< (<<<)) Identity f

reconstituteCtxM :: forall a b m. Bind m => Applicative m =>
  (Context b -> a -> m b) -> Context a -> m (Context b)
reconstituteCtxM = reconstituteCtxFromM Dhall.Context.empty

-- TODO: MonadRec?
reconstituteCtxFromM :: forall a b m. Bind m => Applicative m =>
  Context b -> (Context b -> a -> m b) -> Context a -> m (Context b)
reconstituteCtxFromM ctx0 f = foldr f' (pure ctx0) <<< un Context where
  f' (Tuple name a) mctx = do
    ctx <- mctx
    b <- f ctx a
    pure $ Dhall.Context.insert name b ctx

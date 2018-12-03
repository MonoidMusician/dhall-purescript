module Dhall.TypeCheck where

import Prelude

import Control.Alternative (class Alternative)
import Control.Comonad (extract)
import Control.Comonad.Cofree (Cofree, buildCofree)
import Control.Comonad.Cofree as Cofree
import Control.Comonad.Env (EnvT(..), mapEnvT, runEnvT, withEnvT)
import Control.Monad.Writer (WriterT)
import Control.Plus (empty)
import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Bifoldable (bifoldMap, bifoldl, bifoldr)
import Data.Bifunctor (bimap)
import Data.Bitraversable (bisequence, bitraverse)
import Data.Const as Const
import Data.Foldable (class Foldable, foldMap, foldr, foldl, for_, traverse_)
import Data.FoldableWithIndex (class FoldableWithIndex, foldMapWithIndex, forWithIndex_)
import Data.Function (on)
import Data.Functor.App (App(..))
import Data.Functor.Compose (Compose(..))
import Data.Functor.Mu (Mu)
import Data.Functor.Product (Product(..))
import Data.Functor.Variant (FProxy, SProxy)
import Data.Functor.Variant as VariantF
import Data.FunctorWithIndex (class FunctorWithIndex, mapWithIndex)
import Data.Identity (Identity(..))
import Data.Lazy (Lazy, defer)
import Data.List (List)
import Data.List as List
import Data.List.NonEmpty as NEL
import Data.List.Types (NonEmptyList)
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Maybe.First (First(..))
import Data.Natural (Natural)
import Data.Newtype (class Newtype, un, unwrap, wrap)
import Data.NonEmpty (NonEmpty, (:|))
import Data.Profunctor.Strong ((&&&))
import Data.Semigroup.Foldable (class Foldable1)
import Data.Set (Set)
import Data.Set as Set
import Data.Symbol (class IsSymbol)
import Data.These (These(..), theseLeft)
import Data.Traversable (class Traversable, for, sequence, traverse)
import Data.TraversableWithIndex (forWithIndex)
import Data.Tuple (Tuple(..), curry, uncurry)
import Data.Variant (Variant)
import Data.Variant as Variant
import Dhall.Context (Context)
import Dhall.Context as Dhall.Context
import Dhall.Core as Dhall.Core
import Dhall.Core.AST (Const(..), Expr, ExprRowVFI, Pair(..), S_, _S)
import Dhall.Core.AST as AST
import Dhall.Core.StrMapIsh (class StrMapIsh)
import Dhall.Core.StrMapIsh as StrMapIsh
import Matryoshka (class Corecursive, class Recursive, ana, embed, mapR, project, transCata)
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

-- An expression for the user to look at when an error occurs, giving
-- specific context for what went wrong.
data Focus m a
  -- Atomic: The original tree being typechecked
  = MainExpression
  -- Derived: Pointer to a focus within the prior focus
  | FocusWithin (Lazy ExprRowVFI) (Focus m a)
  -- Derived: Point to the type of another focus
  | TypeOfFocus (Focus m a)
  -- Derived: Point to the same focus but normalized
  | NormalizeFocus (Focus m a)
  -- Atomic: A new expression, whose origin is shrouded in mystery ...
  | ConstructedFocus (Expr m a)

type WR w r = WriterT (Array (Variant w)) (V.Erroring (Variant r))
type Feedback w r m a = WriterT (Array (Variant w)) (V.Erroring (TypeCheckError r (NonEmptyList (Focus m a))))

-- This is a weird kind of catamorphism that lazily gives access to
-- (potentially infinite) applications of itself to its output.
-- `para` on steroids.
recursor :: forall t f m. Recursive t f => Functor m =>
  (f (Cofree m t) -> m t) -> t -> m t
recursor f = go where
  go :: t -> m t
  go e = project e <#> ana (EnvT <<< (identity &&& go)) # f

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
  forall t f m r. Functor m =>
    Recursive r (Compose (Cofree m) f) =>
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

-- Expr with Focus for each node
type Ann m a = Cofree (AST.ExprRowVF m a)
type F = Focus
type D m a = List (Focus m a)
type B m a = NonEmptyList (Focus m a)
type Fxpr m a = Ann m a (F m a)
type Dxpr m a = Ann m a (D m a)
type Bxpr m a = Ann m a (B m a)
-- Expr with Focus and Context
-- (This value if `Let`-bound variable, That type if known)
type Cxpr m a = Cofree (WithBiCtx (AST.ExprRowVF m a))
type Cxpr_ f m a = Cofree (WithBiCtx (AST.ExprRowVF m a)) (f m a)
type CxprB m a = Cxpr_ B m a
type CxprF m a b = EnvT b (WithBiCtx (AST.ExprRowVF m a))
type CxprF_ f m a = EnvT (f m a) (WithBiCtx (AST.ExprRowVF m a))
type CxprFB m a = CxprF_ B m a
type BiContext a = Context (These a a)
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
type Operations w r m a = Product Lazy (Compose Lazy (Feedback w r m a))
-- Expr with Focus and Context, along the dual axes of Operations and the AST
type Oxpr w r m a = TwoD (Operations w r m a) (CxprFB m a)
type Operated w r m a = Cofree (Operations w r m a) (Oxpr w r m a)

typecheckSketch :: forall w r m a. Eq a => StrMapIsh m =>
  (CxprFB m a (Oxpr w r m a) -> Feedback w r m a (CxprB m a)) ->
  CxprB m a -> Oxpr w r m a
typecheckSketch alg = recursor2D \layer@(EnvT (Tuple focus (WithBiCtx ctx e))) -> Product
  let
    ctx' :: Lazy (BiContext (CxprB m a))
    ctx' = defer \_ -> ctx <#> join bimap
      -- Oxpr -> Cxpr
      (head2D)
    reconsitute :: (Focus m a -> Focus m a) -> Expr m a -> CxprB m a
    reconsitute newF e' =
      -- Bxpr -> CxprB
      contextualizeWithin (extract ctx') $
      -- Expr -> Bxpr
      originateFromB (newF <$> focus) $ e'
  in Tuple
      do defer \_ -> reconsitute NormalizeFocus $
          Dhall.Core.normalize $ embed $ e <#>
          -- TODO: preserve spans from original (when possible)
          -- Oxpr -> Cxpr -> Fxpr -> Expr
          (head2D >>> substContext >>> transCata unEnvT)
      do Compose $ defer \_ -> alg layer

normalizeOp :: forall w r m a b. Operations w r m a b -> b
normalizeOp (Product (Tuple lz _)) = extract lz

typecheckOp :: forall w r m a. Operations w r m a ~> Feedback w r m a
typecheckOp (Product (Tuple _ (Compose lz))) = extract lz

normalizeStep :: forall w r m a.
  Oxpr w r m a -> Oxpr w r m a
normalizeStep = step2D >>> normalizeOp

typecheckStep :: forall w r m a.
  Oxpr w r m a -> Feedback w r m a (Oxpr w r m a)
typecheckStep = step2D >>> typecheckOp

topCtxO :: forall w r m a.
  Oxpr w r m a -> BiContext (Oxpr w r m a)
topCtxO = project >>> un Compose >>> extract >>> un EnvT >>> extract >>> getBiCtx

unlayerO :: forall w r m a.
  Oxpr w r m a -> AST.ExprLayerF m a (Oxpr w r m a)
unlayerO = project >>> un Compose >>> extract >>> un EnvT >>> extract >>> dropBiCtx >>> unwrap

topCtx :: forall m a s.
  Cxpr m a s -> BiContext (Cxpr m a s)
topCtx = Cofree.tail >>> getBiCtx

originateFrom :: forall m a. FunctorWithIndex String m =>
  Focus m a -> Expr m a -> Fxpr m a
originateFrom = go where
  go focus e = embed $ EnvT $ Tuple focus $ e # project
    # mapWithIndex \i' -> go $ FocusWithin (pure i') focus

originateFromB :: forall m a. FunctorWithIndex String m =>
  NonEmptyList (Focus m a) -> Expr m a -> Bxpr m a
originateFromB = go where
  go focus e = embed $ EnvT $ Tuple focus $ e # project
    # mapWithIndex \i' -> go $ FocusWithin (pure i') <$> focus

alsoOriginateFrom :: forall m a. FunctorWithIndex String m =>
  NonEmptyList (Focus m a) -> Dxpr m a -> Bxpr m a
alsoOriginateFrom = go where
  go focus e = embed $ e # project
    # withEnvT (NEL.cons' (NEL.head focus) <<< (NEL.tail focus <> _))
    # mapEnvT (mapWithIndex \i' -> go $ FocusWithin (pure i') <$> focus)

-- TODO: use a proper recurrimorphism
contextualizeWithin :: forall m a s. FunctorWithIndex String m =>
  Context (These (Cxpr m a s) (Cxpr m a s)) ->
  Ann m a s -> Cxpr m a s
contextualizeWithin = go where
  go ctx = mapR $ mapEnvT $ (>>>) (un AST.ERVF) $ (<<<) (WithBiCtx ctx <<< AST.ERVF) $ do
    (VariantF.expand <<< map (go ctx))
    # VariantF.onMatch
      { "Let": \(AST.LetF name mty value expr) -> VariantF.inj (_S::S_ "Let")
        let
          mty' = go ctx <$> mty
          value' = go ctx value
          entry = case mty' of
            Nothing -> This value'
            Just ty' -> Both value' ty'
          ctx' = Dhall.Context.insert name entry ctx
          expr' = go ctx' expr
        in AST.LetF name mty' value' expr'
      , "Lam": \(AST.BindingBody name ty body) -> VariantF.inj (_S::S_ "Lam")
        let ty' = go ctx ty
            ctx' = Dhall.Context.insert name (That ty') ctx
        in AST.BindingBody name ty' (go ctx' body)
      , "Pi": \(AST.BindingBody name ty body) -> VariantF.inj (_S::S_ "Pi")
        let ty' = go ctx ty
            ctx' = Dhall.Context.insert name (That ty') ctx
        in AST.BindingBody name ty' (go ctx' body)
      }

noContext :: forall m a s.
  Ann m a s -> Cxpr m a s
noContext = transCata $ mapEnvT (WithBiCtx Dhall.Context.empty)

newborn :: forall m a. FunctorWithIndex String m =>
  Expr m a -> CxprB m a
newborn e0 = e0 # originateFromB (pure (ConstructedFocus e0)) # noContext

newmother :: forall m a.
  AST.ExprLayerF m a (CxprB m a) -> CxprB m a
newmother e0 =
  let e_ = AST.embedW $ e0 <#> dropContext >>> denote
  in embed $
  EnvT (Tuple (pure (ConstructedFocus e_)) (WithBiCtx Dhall.Context.empty (wrap e0)))

denote :: forall m a s.
  Ann m a s -> Expr m a
denote = transCata unEnvT

dropContext :: forall m a s.
  Cxpr m a s -> Ann m a s
dropContext = transCata $ mapEnvT \(WithBiCtx _ e) -> e

plain :: forall m a s. Cxpr m a s -> Expr m a
plain = dropContext >>> denote

substContext :: forall m a s. FunctorWithIndex String m =>
  Cxpr m a s -> Ann m a s
substContext = transCata \(EnvT (Tuple focus (WithBiCtx ctx e))) -> unwrap e #
  VariantF.onMatch
    { "Var": unwrap >>> \(AST.V x n) ->
        case theseLeft =<< Dhall.Context.lookup x n ctx of
          Just value -> project value
          Nothing -> EnvT (Tuple focus e)
    , "Let": \(AST.LetF _ _ _ body) -> project body
    }
    \_ -> EnvT (Tuple focus e)

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

ensureConsistency :: forall w r m a v. StrMapIsh m =>
  (v -> v -> Boolean) ->
  (Inconsistency (NonEmptyList { key :: String, value :: v }) -> Feedback w r m a Void) ->
  m v -> Feedback w r m a Unit
ensureConsistency egal error = traverse_ (map absurd <<< error)
  <<< consistency
  <<< tabulateGroupings egal
  <<< map (uncurry { key: _, value: _ })
  <<< StrMapIsh.toUnfoldable

ensureNodupes :: forall w r m a v i. Ord i => FoldableWithIndex i m =>
  (NonEmptyList i -> Feedback w r m a Void) ->
  m v -> Feedback w r m a Unit
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
  , "Must combine a record" :: Boolean
  , "Record mismatch" :: Unit
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
  , "Unbound variable" :: AST.Var
  , "Annotation mismatch" :: Unit
  , "`Kind` has no type" :: Unit
  , "Unexpected type" :: Boolean
  , "Cannot access" :: String
  , "Constructors requires a union type" :: Unit
  | r
  )
type FeedbackE w r m a = Feedback w (Errors r) m a
type OxprE w r m a = Oxpr w (Errors r) m a

{-| Generalization of `typeWith` that allows type-checking the `Embed`
    constructor with custom logic
-}
typeWithA :: forall w r m a.
  Eq a => StrMapIsh m =>
  Typer m a ->
  Context (Expr m a) ->
  Expr m a ->
  FeedbackE w r m a (Expr m a)
typeWithA tpa ctx e = typecheckSketch typecheckAlgebra
  ( contextualizeWithin (That <<< newborn <$> ctx)
  $ originateFromB (pure MainExpression)
  $ e
  ) # typecheckStep # map (head2D >>> plain)

typecheckAlgebra :: forall w r m a. Eq a => StrMapIsh m =>
  CxprFB m a (OxprE w r m a) -> FeedbackE w r m a (CxprB m a)
typecheckAlgebra (EnvT (Tuple focus (WithBiCtx ctx layer))) = unwrap layer # VariantF.match
  let
    errorHere ::
      forall sym t r' b.
        IsSymbol sym =>
        R.Cons sym t r' (Errors r) =>
      SProxy sym ->
      t ->
      FeedbackE w r m a b
    errorHere sym v = V.liftW $ V.erroring $ TypeCheckError
      { location: focus
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
      { location: focus
      , tag: Variant.inj sym v
      }

    mkFunctor f a = mk (_S::S_ "App") $
      Pair (newborn f) a
    mk :: forall sym f r'.
      Functor f =>
      IsSymbol sym =>
      R.Cons sym (FProxy f) r' (AST.ExprLayerRow m a) =>
      SProxy sym ->
      f (CxprB m a) ->
      CxprB m a
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
      let Pair ty0' ty1' = Pair ty0 ty1 <#> normalizeStep >>> head2D >>> plain in
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
      FeedbackE w r m a (CxprB m a)
    onConst f (Const.Const c) = f c <#> newborn
    always :: forall y. Expr m a -> y -> FeedbackE w r m a (CxprB m a)
    always b _ = pure $ newborn $ b
    aType :: forall x. Const.Const x (OxprE w r m a) -> FeedbackE w r m a (CxprB m a)
    aType = always $ AST.mkType
    aFunctor :: forall x. Const.Const x (OxprE w r m a) -> FeedbackE w r m a (CxprB m a)
    aFunctor = always $ AST.mkArrow AST.mkType AST.mkType
    a0 = AST.mkVar (AST.V "a" 0)

    -- TODO: This will need to become aware of AST holes
    -- Check a binary operation (`Pair` functor) against a simple, static,
    -- *normalized* type `t`.
    checkBinOp ::
      Expr m a ->
      Pair (OxprE w r m a) ->
      FeedbackE w r m a (CxprB m a)
    checkBinOp t p = suggest (newborn t) $ forWithIndex_ p $
      -- t should be simple enough that alphaNormalize is unnecessary
      \side operand -> typecheckStep operand >>= normalizeStep >>> case _ of
        ty_operand | t == plain (head2D ty_operand) -> pure unit
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
          let name0 = AST.V name 0 in
          if Dhall.Core.judgmentallyEqual (plain $ head2D aty0) (plain $ head2D aty1)
            then do
              pure $ mk(_S::S_"App") $ Pair
                do mk(_S::S_"Lam") (head2D <$> AST.BindingBody name aty0 rty)
                do head2D aty1
            else do
              -- SPECIAL!
              -- Recovery case: if the variable is free in the return type
              -- then this is a non-dependent function
              -- and its return type can be suggested
              -- even if its argument does not have the right type
              -- TODO: use algebra
              (if not Dhall.Core.freeIn name0 (plain $ head2D rty) then suggest (head2D rty) else identity) $
                errorHere (_S::S_ "Type mismatch") unit
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
        combineTypes (p :: Pair (OxprE w r m a)) = do
          AST.Pair { const: constL, kts: ktsL } { const: constR, kts: ktsR } <-
            forWithIndex p \side ty -> do
              kts <- ensure' (_S::S_ "Record") ty
                (errorHere (_S::S_ "Must combine a record") <<< const side)
              kind <- typecheckStep ty
              const <- ensureConst kind
                (errorHere (_S::S_ "Must combine a record") <<< const side)
              pure { kts, const }
          when (constL /= constR) $ errorHere (_S::S_ "Record mismatch") unit
          let combined = StrMapIsh.unionWith (pure pure) ktsL ktsR
          mk(_S::S_"Record") <$> forWithIndex combined \k ->
            case _ of
              Both ktsL' ktsR' ->
                -- TODO: scope
                combineTypes (AST.Pair ktsL' ktsR')
              This t -> pure (head2D t)
              That t -> pure (head2D t)
      in (=<<) combineTypes <<< traverse typecheckStep
  , "CombineTypes":
      let
        combineTypes (p :: Pair (OxprE w r m a)) = do
          AST.Pair { const: constL, kts: ktsL } { const: constR, kts: ktsR } <-
            forWithIndex p \side ty -> do
              kts <- ensure' (_S::S_ "Record") ty
                (errorHere (_S::S_ "Must combine a record") <<< const side)
              kind <- typecheckStep ty
              const <- ensureConst kind
                (errorHere (_S::S_ "Must combine a record") <<< const side)
              pure { kts, const }
          when (constL /= constR) $ errorHere (_S::S_ "Record mismatch") unit
          let combined = StrMapIsh.unionWith (pure pure) ktsL ktsR
          mk(_S::S_"Record") <$> forWithIndex combined \k ->
            case _ of
              Both ktsL' ktsR' ->
                -- TODO: scope
                combineTypes (AST.Pair ktsL' ktsR')
              This t -> pure (head2D t)
              That t -> pure (head2D t)
      in combineTypes
  , "Prefer": \p -> do
      AST.Pair { const: constL, kts: ktsL } { const: constR, kts: ktsR } <-
        forWithIndex p \side kvs -> do
          ty <- typecheckStep kvs
          kts <- ensure' (_S::S_ "Record") ty
            (errorHere (_S::S_ "Must combine a record") <<< const side)
          k <- typecheckStep ty
          const <- unwrap <$> ensure (_S::S_ "Const") ty
            (errorHere (_S::S_ "Must combine a record") <<< const side)
          pure { kts, const }
      when (constL /= constR) $ errorHere (_S::S_ "Record mismatch") unit
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
            -- FIXME NOTE: the following check added
            when (Dhall.Core.freeIn (AST.V name 0) (plain $ head2D output))
              (errorHere (_S::S_ "Dependent handler function") <<< const k $ unit)
            pure output
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
            -- FIXME NOTE: the following check added
            when (Dhall.Core.freeIn (AST.V name 0) (plain $ head2D output))
              (errorHere (_S::S_ "Dependent handler function") <<< const k $ unit)
            checkEq ty output
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
          -- FIXME
          -- _ <- loop ctx t
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
                Type -> expr # unlayerO #
                  VariantF.on (_S::S_ "Union") handleType (\_ -> error unit)
                _ -> error unit
      tyR # normalizeStep # unlayerO # casing
  , "Project": \(Tuple (App ks) expr) -> do
      kts <- ensure (_S::S_ "Record") expr
        (errorHere (_S::S_ "Cannot project"))
      -- FIXME
      -- _ <- loop ctx t
      mk(_S::S_"Record") <<< map head2D <$> forWithIndex ks \k (_ :: Unit) ->
        StrMapIsh.get k kts #
          (noteHere (_S::S_ "Missing field") k)
  , "ImportAlt": \(Pair l _r) ->
      -- FIXME???
      head2D <$> typecheckStep l
  , "Embed": errorHere (_S::S_ "Oops") <<< const unit -- TODO
  }

-- The explanation, given as text interspersed with specific places to look at
-- (for the user to read)
explain ::
  forall m a.
    StrMapIsh m =>
  Expr m a ->
  Variant (Errors ()) ->
  AST.TextLitF (Focus m a)
explain origin =
  let errorUnknownError = AST.TextLit "Sorry I don’t know how to explain this error"
      nodeType = AST.projectW origin
  in
  Variant.default errorUnknownError

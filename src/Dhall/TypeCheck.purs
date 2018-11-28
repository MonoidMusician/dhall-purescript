module Dhall.TypeCheck where

import Prelude

import Control.Alternative (class Alternative)
import Control.Comonad (class Comonad, extract)
import Control.Comonad.Cofree (Cofree, buildCofree, hoistCofree)
import Control.Comonad.Cofree as Cofree
import Control.Comonad.Env (EnvT(..), mapEnvT, runEnvT)
import Control.Monad.Reader (ReaderT(..), mapReaderT, runReaderT)
import Control.Monad.Writer (WriterT, mapWriterT)
import Control.Plus (empty)
import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Bifoldable (bifoldMap, bifoldl, bifoldr)
import Data.Bifunctor (bimap, lmap)
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
import Data.These (These(..))
import Data.Traversable (class Traversable, for, sequence, traverse)
import Data.TraversableWithIndex (forWithIndex)
import Data.Tuple (Tuple(..), curry, uncurry)
import Data.Variant (Variant)
import Data.Variant as Variant
import Dhall.Context (Context)
import Dhall.Context as Dhall.Context
import Dhall.Core as Dhall.Core
import Dhall.Core.AST (_S, S_, Const(..), Expr, ExprRowVFI(..), Pair(..))
import Dhall.Core.AST as AST
import Dhall.Core.AST.Noted as Ann
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

newtype TypeCheckError r m a = TypeCheckError
  -- The main location where the typechecking error occurred
  { location :: Focus m a
  -- The tag for the specific error, mostly for machine purposes
  , tag :: Variant r
  }

mapFocus :: forall r m a m' a'.
  (Focus m a -> Focus m' a') ->
  TypeCheckError r m a -> TypeCheckError r m' a'
mapFocus f (TypeCheckError e) = TypeCheckError (e { location = f e.location })

errorSimple ::
  forall sym t r r' w m a b.
    IsSymbol sym =>
    R.Cons sym t r' r =>
  SProxy sym ->
  t ->
  Feedback w r m a b
errorSimple sym v = V.liftW $ V.erroring $ TypeCheckError
  { location: MainExpression
  , tag: Variant.inj sym v
  }

noteSimple ::
  forall sym t r r' w m a b.
    IsSymbol sym =>
    R.Cons sym t r' r =>
  SProxy sym ->
  t ->
  Maybe b ->
  Feedback w r m a b
noteSimple sym v = (<<<) V.liftW $ V.note $ TypeCheckError
  { location: MainExpression
  , tag: Variant.inj sym v
  }

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

type Ctx m a = Context (Expr m a)
type Feedback w r m a = WriterT (Array (Variant w)) (V.Erroring (TypeCheckError r m a))
type CtxFeedback w r m a = ReaderT (Ctx m a) (Feedback w r m a)
type TypeChecked w r m a = Feedback w r m a (Expr m a)
type CtxTypeChecked w r m a = CtxFeedback w r m a (Expr m a)
type Shallot w r m a = Cofree (Feedback w r m a) (Expr m a)
-- A shallot only has one context for the term, type, and kind
type CtxShallot w r m a = Cofree (ReaderT (Ctx m a) (Feedback w r m a)) (Expr m a)

-- This is `lift` for `ReaderT`, without the (`Monad`) constraints.
oblivious :: forall w r m a. Feedback w r m a ~> CtxFeedback w r m a
oblivious = ReaderT <<< const

-- This is the proper way to introduce a type into the context.
intro :: forall w r m a. StrMapIsh m => Eq a => String -> CtxShallot w r m a -> Ctx m a -> Ctx m a
intro name ty ctx =
  Dhall.Core.shift 1 (AST.V name 0) <$>
    Dhall.Context.insert name (Dhall.Core.normalize (extract ty)) ctx

-- This is `local` for `ReaderT`, without the (`Monad`) constraints.
localize :: forall w r m a. (Ctx m a -> Ctx m a) -> CtxFeedback w r m a ~> CtxFeedback w r m a
localize f act = ReaderT $ f >>> runReaderT act

introize :: forall w r m a. StrMapIsh m => Eq a => String -> CtxShallot w r m a -> CtxFeedback w r m a ~> CtxFeedback w r m a
introize name ty = localize (intro name ty)

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
  go = ana $ (<<<) Compose $ buildCofree do
    project &&& \t -> project t <#> go # f

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

-- Expr with Focus for each node
type Fxpr m a = Ann.Expr m (Focus m a) a
-- Expr with Focus and Context
-- (This value if `Let`-bound variable, That type if known)
type Cxpr m a = Cofree (WithBiCtx (AST.ExprRowVF m a)) (Focus m a)
type CxprF m a = EnvT (Focus m a) (WithBiCtx (AST.ExprRowVF m a))
type BiContext a = Context (These a a)
-- Product (Compose Context (Join These)) f, but without the newtypes
data WithBiCtx f a = WithBiCtx (BiContext a) (f a)
getBiCtx :: forall f a. WithBiCtx f a -> BiContext a
getBiCtx (WithBiCtx ctx _) = ctx
dropBiCtx :: forall f a. WithBiCtx f a -> f a
dropBiCtx (WithBiCtx _ fa) = fa
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
--   Left (Lazy): normalization (idempotent, but this isn't enforced ...)
--   Right (Lazy Feedback): typechecking
type Operations w r m a = Product Lazy (Compose Lazy (Feedback w r m a))
-- Expr with Focus and Context, along the dual axes of Operations and the AST
type Oxpr w r m a = TwoD (Operations w r m a) (CxprF m a)
type Operated w r m a = Cofree (Operations w r m a) (Oxpr w r m a)

typecheckSketch :: forall w r m a. Eq a => StrMapIsh m =>
  (AST.ExprRowVF m a (Oxpr w r m a) -> TypeChecked w r m a) ->
  Cxpr m a -> Oxpr w r m a
typecheckSketch typecheckAlgorithm = recursor2D \(EnvT (Tuple focus (WithBiCtx ctx e))) -> Product
  let
    ctx' :: Lazy (BiContext (Cxpr m a))
    ctx' = defer \_ -> ctx <#> join bimap
      -- Oxpr -> Cxpr
      (head2D)
    reconsitute :: (Focus m a -> Focus m a) -> Expr m a -> Cxpr m a
    reconsitute newF e' =
      -- Fxpr -> Cxpr
      contextualizeWithin (extract ctx') $
      -- Expr -> Fxpr
      originateFrom (newF focus) $ e'
  in Tuple
      do defer \_ -> reconsitute NormalizeFocus $
          Dhall.Core.normalize $ embed $ e <#>
          -- Oxpr -> Cxpr -> Fxpr -> Expr
          (head2D >>> dropContext >>> dropOrigin)
      do Compose $ defer \_ -> reconsitute TypeOfFocus <$>
          typecheckAlgorithm e

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
  Oxpr w r m a -> AST.ExprRowVF m a (Oxpr w r m a)
unlayerO = project >>> un Compose >>> extract >>> un EnvT >>> extract >>> dropBiCtx

topCtx :: forall m a.
  Cxpr m a -> BiContext (Cxpr m a)
topCtx = Cofree.tail >>> getBiCtx

originateFrom :: forall m a. FunctorWithIndex String m =>
  Focus m a -> Expr m a -> Fxpr m a
originateFrom = go where
  go focus e = embed $ EnvT $ Tuple focus $ e # project
    # mapWithIndex \i' -> go $ FocusWithin (pure i') focus

contextualizeWithin :: forall m a. FunctorWithIndex String m =>
  Context (These (Cxpr m a) (Cxpr m a)) ->
  Fxpr m a -> Cxpr m a
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

dropOrigin :: forall m a. FunctorWithIndex String m =>
  Fxpr m a -> Expr m a
dropOrigin = transCata $ runEnvT >>> extract

dropContext :: forall m a. FunctorWithIndex String m =>
  Cxpr m a -> Fxpr m a
dropContext = transCata $ mapEnvT \(WithBiCtx _ e) -> e

-- typecheck :: forall w r m a. Shallot w r m a -> TypeChecked w r m a
-- typecheck :: forall w r m a. CtxShallot w r m a -> CtxTypeChecked w r m a
typecheck :: forall f a. Functor f => Cofree f a -> f a
typecheck s = Cofree.tail s <#> extract

-- kindcheck :: forall w r m a. Shallot w r m a -> TypeChecked w r m a
-- kindcheck :: forall w r m a. CtxShallot w r m a -> CtxTypeChecked w r m a
kindcheck :: forall f a. Bind f => Cofree f a -> f a
kindcheck s = Cofree.tail s >>= typecheck

-- term :: forall w r m a. Shallot w r m a -> Expr m a
-- term :: forall w r m a. CtxShallot w r m a -> Expr m a
term :: forall m a. Comonad m => m a -> a
term = extract

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
type FeedbackE w r m a = WriterT (Array (Variant w)) (V.Erroring (TypeCheckError (Errors r) m a))
type CtxFeedbackE w r m a = ReaderT (Ctx m a) (FeedbackE w r m a)
type TypeCheckedE w r m a = FeedbackE w r m a (Expr m a)
type CtxTypeCheckedE w r m a = CtxFeedbackE w r m a (Expr m a)
type ShallotE w r m a = Cofree (FeedbackE w r m a) (Expr m a)
type CtxShallotE w r m a = Cofree (ReaderT (Ctx m a) (FeedbackE w r m a)) (Expr m a)

{-| Generalization of `typeWith` that allows type-checking the `Embed`
    constructor with custom logic
-}
typeWithA :: forall w r m a.
  Eq a => StrMapIsh m =>
  Typer m a ->
  Context (Expr m a) ->
  Expr m a ->
  TypeCheckedE w r m a
typeWithA tpa = flip $ compose runReaderT $ recursor $
  let
    -- Tag each error/warning with the index at which it occurred, recursively
    indexFeedback :: ExprRowVFI -> FeedbackE w r m a ~> FeedbackE w r m a
    indexFeedback i =
      mapWriterT (lmap (mapFocus (FocusWithin (pure i))))
    -- TODO: is this right?
    indexFeedbackCF :: CtxShallotE w r m a -> CtxShallotE w r m a
    indexFeedbackCF = hoistCofree (mapReaderT (mapWriterT (lmap (mapFocus TypeOfFocus))))
  in
  -- Before we pass it to the handler below, tag indices and then unwrap it
  (>>>) (mapWithIndex (\i -> indexFeedbackCF <<< hoistCofree (mapReaderT (indexFeedback i)))) $
  (>>>) unwrap $
  let
    ensure' :: forall sym f r'.
      IsSymbol sym =>
      R.Cons sym (FProxy f) r' (AST.ExprLayerRow m a) =>
      SProxy sym ->
      Expr m a ->
      (Unit -> FeedbackE w r m a Void) ->
      FeedbackE w r m a (f (Expr m a))
    ensure' s ty error =
      let nf_ty = Dhall.Core.normalize ty in
      AST.projectW nf_ty # VariantF.on s pure
        \_ -> absurd <$> error unit

    checkEq ::
      Expr m a -> Expr m a ->
      (Unit -> FeedbackE w r m a Void) ->
      FeedbackE w r m a Unit
    checkEq ty0 ty1 error =
      when (not Dhall.Core.judgmentallyEqual ty0 ty1) $
        absurd <$> error unit
    checkEqL ::
      Expr m a -> Expr m a ->
      (Unit -> FeedbackE w r m a Void) ->
      FeedbackE w r m a (Expr m a)
    checkEqL ty0 ty1 error = suggest ty0 $ checkEq ty0 ty1 error
    checkEqR ::
      Expr m a -> Expr m a ->
      (Unit -> FeedbackE w r m a Void) ->
      FeedbackE w r m a (Expr m a)
    checkEqR ty0 ty1 error = suggest ty1 $ checkEq ty0 ty1 error
  in let
    contextual =
      let
        ensureConst_ctx ::
          CtxShallotE w r m a ->
          (Unit -> FeedbackE w r m a Void) ->
          CtxFeedbackE w r m a Const
        ensureConst_ctx expr error = do
          ty <- typecheck expr
          oblivious $ unwrap <$> ensure' (_S::S_ "Const") ty error
      in
      { "Const": unwrap >>> \c ->
          axiom c <#> AST.mkConst #
            oblivious <<< noteSimple (_S::S_ "`Kind` has no type") unit
      , "Var": unwrap >>> \v@(AST.V name idx) -> ReaderT \ctx ->
          Dhall.Context.lookup name idx ctx #
            noteSimple (_S::S_ "Unbound variable") v
      , "Lam": \(AST.BindingBody name ty body) -> do
          kA <- ensureConst_ctx ty
            (errorSimple (_S::S_ "Invalid input type"))
          -- normalize (as part of `intro`) _after_ typechecking succeeds
          -- (in order to guarantee that normalization terminates)
          introize name ty do
            ty_body <- Cofree.tail body
            kB <- ensureConst_ctx ty_body
              (errorSimple (_S::S_ "Invalid output type"))
            _ <- rule kA kB #
              oblivious <<< noteSimple (_S::S_ "No dependent types") unit
            pure $ AST.mkPi name (term ty) (term ty_body)
      , "Pi": \(AST.BindingBody name ty ty_body) -> do
          kA <- ensureConst_ctx ty
            (errorSimple (_S::S_ "Invalid input type"))
          -- normalize (as part of `intro`) _after_ typechecking succeeds
          -- (in order to guarantee that normalization terminates)
          introize name ty do
            kB <- ensureConst_ctx ty_body
              (errorSimple (_S::S_ "Invalid output type"))
            map AST.mkConst $ rule kA kB #
              oblivious <<< noteSimple (_S::S_ "No dependent types") unit
      , "Let": \(AST.LetF name mty value expr) -> do
          ty0 <- Cofree.tail value
          ty <- fromMaybe ty0 <$> for mty \ty' -> do
            _ <- typecheck ty'
            oblivious $ ty' <$ checkEq (term ty0) (term ty')
              (errorSimple (_S::S_ "Annotation mismatch"))
          kind <- typecheck ty
          let
            name0 = AST.V name 0
            shiftIn = Dhall.Core.shift 1 name0
            shiftOut = Dhall.Core.shift (-1) name0
            subst = Dhall.Core.subst name0 $ shiftIn $ Dhall.Core.normalize $ term value
            substShiftOut = subst >>> shiftOut
          let
            -- The catch-all branch directly implements the Dhall
            -- specification as written; it is necessary to substitute in
            -- types in order to get 'dependent let' behaviour and to
            -- allow type synonyms (see #69). However, doing a full
            -- substitution is slow if the value is large and used many
            -- times. If the value being substitued in is a term (i.e.,
            -- its type is a Type), then we can get a very significant
            -- speed-up by doing the type-checking once at binding-time,
            -- as opposed to doing it at every use site (see #412).

            -- TODO: Does this apply to Kind too?
            handleType Type = do
              introize name ty $ typecheck expr <#> substShiftOut
            handleType _ = fallback unit

            fallback _ = ReaderT \ctx ->
              -- FIXME 👻
              typeWithA tpa ctx (substShiftOut (term expr))
          kind # Dhall.Core.normalize # AST.projectW #
            VariantF.on (_S::S_ "Const")
              (unwrap >>> handleType)
              \_ -> fallback unit
      }
    preservative =
      let
        onConst :: forall x.
          (x -> FeedbackE w r m a (Expr m a)) ->
          Const.Const x (ShallotE w r m a) ->
          TypeCheckedE w r m a
        onConst f (Const.Const c) = f c
        always :: forall x y. x -> y -> FeedbackE w r m a x
        always b _ = pure b
        aType :: forall x. Const.Const x (ShallotE w r m a) -> TypeCheckedE w r m a
        aType = always $ AST.mkType
        aFunctor :: forall x. Const.Const x (ShallotE w r m a) -> TypeCheckedE w r m a
        aFunctor = always $ AST.mkArrow AST.mkType AST.mkType
        a0 = AST.mkVar (AST.V "a" 0)

        -- TODO: This will need to become aware of AST holes
        -- Check a binary operation (`Pair` functor) against a simple, static,
        -- *normalized* type `t`.
        checkBinOp ::
          Expr m a ->
          Pair (ShallotE w r m a) ->
          TypeCheckedE w r m a
        checkBinOp t p = suggest t $ forWithIndex_ p $
          -- t should be simple enough that alphaNormalize is unnecessary
          \side operand -> typecheck operand >>= Dhall.Core.normalize >>> case _ of
            ty_operand | t == ty_operand -> pure unit
              | otherwise -> errorSimple
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
          ShallotE w r m a ->
          (Unit -> FeedbackE w r m a Void) ->
          FeedbackE w r m a (f (Expr m a))
        ensure s expr error = do
          ty <- typecheck expr
          ensure' s ty error

        -- Ensure that the passed `expr` is a term; i.e. the type of its type
        -- is `Type`. Returns the type of the `expr`.
        ensureTerm ::
          ShallotE w r m a ->
          (Unit -> FeedbackE w r m a Void) ->
          FeedbackE w r m a (Expr m a)
        ensureTerm expr error = do
          ty <- Cofree.tail expr
          term ty <$ ensureType ty error

        -- Ensure that the passed `ty` is a type; i.e. its type is `Type`.
        ensureType ::
          ShallotE w r m a ->
          (Unit -> FeedbackE w r m a Void) ->
          FeedbackE w r m a Unit
        ensureType ty error = do
          kind <- typecheck ty
          ensure' (_S::S_ "Const") kind error >>= case _ of
            Const.Const Type -> pure unit
            _ -> absurd <$> error unit
      in
      { "App": \(AST.Pair f a) ->
          let
            checkFn = ensure (_S::S_ "Pi") f
              (errorSimple (_S::S_ "Not a function"))
            checkArg (AST.BindingBody name aty0 rty) aty1 =
              let name0 = AST.V name 0 in
              if Dhall.Core.judgmentallyEqual aty0 aty1
                then do
                  pure $ Dhall.Core.shiftSubstShift0 name (term a) rty
                else do
                  -- SPECIAL!
                  -- Recovery case: if the variable is free in the return type
                  -- then this is a non-dependent function
                  -- and its return type can be suggested
                  -- even if its argument does not have the right type
                  (if not Dhall.Core.freeIn name0 rty then suggest rty else identity) $
                    errorSimple (_S::S_ "Type mismatch") unit
          in join $ checkArg <$> checkFn <*> typecheck a
      , "Annot": \(AST.Pair expr ty) -> suggest (term ty) $
          join $ checkEq
            <$> typecheck expr
            <@> term ty
            <@> errorSimple (_S::S_ "Annotation mismatch")
            <* typecheck ty
      , "Bool": identity aType
      , "BoolLit": always $ AST.mkBool
      , "BoolAnd": checkBinOp AST.mkBool
      , "BoolOr": checkBinOp AST.mkBool
      , "BoolEQ": checkBinOp AST.mkBool
      , "BoolNE": checkBinOp AST.mkBool
      , "BoolIf": \(AST.Triplet c t f) ->
          ensure (_S::S_ "Bool") c
            (errorSimple (_S::S_ "Invalid predicate")) *> do
          join $ checkEqL
              <$> ensureTerm t
                (errorSimple (_S::S_ "If branch must be term") <<< const false)
              <*> ensureTerm f
                (errorSimple (_S::S_ "If branch must be term") <<< const true)
              <@> errorSimple (_S::S_ "If branch mismatch")
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
      , "TextLit": \things -> suggest AST.mkText $
          forWithIndex_ things \i expr -> ensure (_S::S_ "Text") expr
            (errorSimple (_S::S_ "Cannot interpolate") <<< const i)
      , "TextAppend": checkBinOp AST.mkText
      , "List": identity aFunctor
      , "ListLit": \(Product (Tuple mty lit)) -> AST.mkApp AST.mkList <$> do
          -- get the assumed type of the list
          (ty :: Expr m a) <- case mty of
            -- either from annotation
            Just ty -> suggest (term ty) $
              ensureType ty
                (errorSimple (_S::S_ "Invalid list type"))
            -- or from the first element
            Nothing -> case Array.head lit of
              Nothing -> errorSimple (_S::S_ "Missing list type") $ unit
              Just item -> do
                ensureTerm item
                  (errorSimple (_S::S_ "Invalid list type"))
          suggest ty $ forWithIndex_ lit \i item -> do
            ty' <- typecheck item
            checkEq ty ty' \_ ->
              case mty of
                Nothing ->
                  errorSimple (_S::S_ "Invalid list element") $ i
                Just _ ->
                  errorSimple (_S::S_ "Mismatched list elements") $ i
      , "ListAppend": \p -> AST.mkApp AST.mkList <$> do
          AST.Pair ty_l ty_r <- forWithIndex p \side expr -> do
            let error = errorSimple (_S::S_ "Cannot append non-list") <<< const side
            expr_ty <- typecheck expr
            AST.Pair list ty <- ensure' (_S::S_ "App") expr_ty error
            Dhall.Core.normalize list # AST.projectW #
              VariantF.on (_S::S_ "List") (const (pure unit))
                \_ -> absurd <$> error unit
            pure ty
          checkEqL ty_l ty_r
            (errorSimple (_S::S_ "List append mismatch"))
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
            (errorSimple (_S::S_ "Invalid optional type"))
          suggest (AST.mkApp AST.mkOptional (term ty)) $
            for_ mexpr \expr -> do
              join $ checkEq (term ty)
                <$> typecheck expr
                <@> (errorSimple (_S::S_ "Invalid optional element"))
      , "Some": unwrap >>> \a ->
          AST.mkApp AST.mkOptional <$> ensureTerm a
            (errorSimple (_S::S_ "Invalid `Some`"))
      , "OptionalFold": always $ AST.mkForall "a" $
          AST.mkArrow (AST.mkApp AST.mkOptional a0) (optionalEnc a0)
      , "OptionalBuild": always $ AST.mkForall "a" $
          AST.mkArrow (optionalEnc a0) (AST.mkApp AST.mkOptional a0)
      , "Record": \kts ->
          ensureNodupes
            (errorSimple (_S::S_ "Duplicate record fields")) kts
          *> do
            kts' <- forWithIndex kts \field ty -> do
              c <- unwrap <$> ensure (_S::S_ "Const") ty
                (errorSimple (_S::S_ "Invalid field type") <<< const field)
              case c of
                Kind ->
                  checkEq AST.mkType (term ty)
                    (errorSimple (_S::S_ "Invalid field type") <<< const field)
                _ -> pure unit
              pure { kind: c, ty: term ty }
            ensureConsistency (eq `on` _.kind)
              (errorSimple (_S::S_ "Inconsistent field types") <<< (map <<< map) _.key) kts'
            pure $ AST.mkConst $ maybe Type _.kind $ un First $ foldMap pure kts'
      , "RecordLit": \kvs ->
          ensureNodupes
            (errorSimple (_S::S_ "Duplicate record fields")) kvs
          *> do
            kts <- traverse Cofree.tail kvs
            suggest (AST.mkRecord (term <$> kts)) do
              kts' <- forWithIndex kts \field ty -> do
                c <- unwrap <$> ensure (_S::S_ "Const") ty
                  (errorSimple (_S::S_ "Invalid field type") <<< const field)
                case c of
                  Kind ->
                    checkEq AST.mkType (term ty)
                      (errorSimple (_S::S_ "Invalid field type") <<< const field)
                  _ -> pure unit
                pure { kind: c, ty: term ty }
              ensureConsistency (eq `on` _.kind)
                (errorSimple (_S::S_ "Inconsistent field types") <<< (map <<< map) _.key) kts'
      , "Union": \kts ->
          ensureNodupes
            (errorSimple (_S::S_ "Duplicate union fields")) kts
          *> do
            -- FIXME: should this be the largest of `Type` or `Kind` returned?
            suggest AST.mkType $
              forWithIndex_ kts \field ty -> do
                void $ ensure (_S::S_ "Const") ty
                  (errorSimple (_S::S_ "Invalid alternative type") <<< const field)
      , "UnionLit": \(Product (Tuple (Tuple field expr) kts)) ->
          ensureNodupes
            (errorSimple (_S::S_ "Duplicate union fields")) kts
          *> do
            ty <- Cofree.tail expr
            let kts' = StrMapIsh.insert field ty kts
            forWithIndex_ kts' \field' kind -> do
              void $ ensure (_S::S_ "Const") kind
                (errorSimple (_S::S_ "Invalid alternative type") <<< const field')
            pure $ AST.mkUnion $ term <$> kts'
      , "Combine": \p -> do
          AST.Pair { const: constL, kts: ktsL } { const: constR, kts: ktsR } <-
            forWithIndex p \side ty -> do
              kalls <- { ty: _, kind: _ } <$> typecheck ty <*> kindcheck ty
              kts <- ensure' (_S::S_ "Record") kalls.ty
                (errorSimple (_S::S_ "Must combine a record") <<< const side)
              const <- unwrap <$> ensure' (_S::S_ "Const") kalls.kind
                (errorSimple (_S::S_ "Must combine a record") <<< const side)
              pure { kts, const }
          -- kind checking only needs to occur at the top level
          -- since nested records will have the same (compatible) kinds
          when (constL /= constR) $ errorSimple (_S::S_ "Record mismatch") unit
          let
            combineTypes (p' :: Pair (Expr m a)) = do
              AST.Pair ktsL' ktsR' <-
                forWithIndex p' \side ty -> do
                  ensure' (_S::S_ "Record") ty
                    (errorSimple (_S::S_ "Must combine a record") <<< const side)
              let combined = StrMapIsh.unionWith (pure pure) ktsL' ktsR'
              AST.mkRecord <$> forWithIndex combined \k ->
                case _ of
                  Both ktsL'' ktsR'' ->
                    -- TODO: scope
                    indexFeedback (ERVFI (Variant.inj (_S::S_ "Record") k)) $
                      combineTypes (AST.Pair ktsL'' ktsR'')
                  This t -> pure t
                  That t -> pure t
          -- so just pass the types now
          combineTypes =<< traverse typecheck p
      , "CombineTypes": \p -> do
          AST.Pair { const: constL, kts: ktsL } { const: constR, kts: ktsR } <-
            forWithIndex p \side ty -> do
              kalls <- { ty: _, kind: _ } <$> pure (term ty) <*> typecheck ty
              kts <- ensure' (_S::S_ "Record") kalls.ty
                (errorSimple (_S::S_ "Must combine a record") <<< const side)
              const <- unwrap <$> ensure' (_S::S_ "Const") kalls.kind
                (errorSimple (_S::S_ "Must combine a record") <<< const side)
              pure { kts, const }
          -- kind checking only needs to occur at the top level
          -- since nested records will have the same (compatible) kinds
          when (constL /= constR) $ errorSimple (_S::S_ "Record mismatch") unit
          AST.mkConst constL <$ do
            let
              combineTypes (p' :: Pair (Expr m a)) = do
                AST.Pair ktsL' ktsR' <-
                  forWithIndex p' \side ty -> do
                    ensure' (_S::S_ "Record") ty
                      (errorSimple (_S::S_ "Must combine a record") <<< const side)
                let combined = StrMapIsh.unionWith (pure pure) ktsL' ktsR'
                AST.mkRecord <$> forWithIndex combined \k ->
                  case _ of
                    Both ktsL'' ktsR'' ->
                      -- TODO: scope
                      indexFeedback (ERVFI (Variant.inj (_S::S_ "Record") k)) $
                        combineTypes (AST.Pair ktsL'' ktsR'')
                    This t -> pure t
                    That t -> pure t
            -- so just pass the types now
            combineTypes (term <$> p)
      , "Prefer": \p -> do
          AST.Pair { const: constL, kts: ktsL } { const: constR, kts: ktsR } <-
            forWithIndex p \side kvs -> do
              ty <- Cofree.tail kvs
              kts <- ensure' (_S::S_ "Record") (term ty)
                (errorSimple (_S::S_ "Must combine a record") <<< const side)
              k <- typecheck ty
              const <- unwrap <$> ensure (_S::S_ "Const") ty
                (errorSimple (_S::S_ "Must combine a record") <<< const side)
              pure { kts, const }
          when (constL /= constR) $ errorSimple (_S::S_ "Record mismatch") unit
          let
            preference = Just <<< case _ of
              This a -> a
              That b -> b
              Both a _ -> a
          pure $ AST.mkRecord $ StrMapIsh.unionWith (pure preference) ktsR ktsL
      , "Merge": \(AST.MergeF handlers cases mty) -> do
          Pair ktsX ktsY <- Pair
            <$> ensure (_S::S_ "Record") handlers
              (errorSimple (_S::S_ "Must merge a record"))
            <*> ensure (_S::S_ "Union") cases
              (errorSimple (_S::S_ "Must merge a union"))
          let
            ksX = unit <$ ktsX # Set.fromFoldable
            ksY = unit <$ ktsY # Set.fromFoldable
            diffX = Set.difference ksX ksY
            diffY = Set.difference ksY ksX
          -- get the assumed type of the merge result
          (ty :: Expr m a) <- case mty of
            -- either from annotation
            Just ty -> pure (term ty)
            -- or from the first handler
            Nothing -> case un First $ foldMapWithIndex (curry pure) ktsX of
              Nothing -> errorSimple (_S::S_ "Missing merge type") $ unit
              Just (Tuple k item) -> do
                AST.BindingBody name _ output <- ensure' (_S::S_ "Pi") item
                  (errorSimple (_S::S_ "Handler not a function") <<< const k)
                -- NOTE: the following check added
                when (Dhall.Core.freeIn (AST.V name 0) output)
                  (errorSimple (_S::S_ "Dependent handler function") <<< const k $ unit)
                pure $ Dhall.Core.shift (-1) (AST.V name 0) output
          forWithIndex_ ktsY \k tY -> do
            tX <- StrMapIsh.get k ktsX #
              noteSimple (_S::S_ "Missing handler") diffX
            AST.BindingBody name input output <- ensure' (_S::S_ "Pi") tX
              (errorSimple (_S::S_ "Handler not a function") <<< const k)
            ado
              checkEq tY input
                (errorSimple (_S::S_ "Handler input type mismatch") <<< const k)
            in do
              -- NOTE: the following check added
              when (Dhall.Core.freeIn (AST.V name 0) output)
                (errorSimple (_S::S_ "Dependent handler function") <<< const k $ unit)
              let output' = Dhall.Core.shift (-1) (AST.V name 0) output
              checkEq ty output'
                (errorSimple (_S::S_ "Handler output type mismatch") <<< const k)
          suggest ty $
            when (not Set.isEmpty diffX)
              (errorSimple (_S::S_ "Unused handlers") diffX)
      , "Constructors": \(Identity ty) -> do
          void $ typecheck ty
          kts <- term ty # Dhall.Core.normalize # AST.projectW #
            VariantF.on (_S::S_ "Union") pure
              \_ -> errorSimple (_S::S_ "Constructors requires a union type") $ unit
          pure $ AST.mkRecord $ kts # mapWithIndex \field ty' ->
            AST.mkPi field ty' $ term ty
      , "Field": \(Tuple field expr) -> do
          tyR <- typecheck expr
          let
            error _ = errorSimple (_S::S_ "Cannot access") $ field
            handleRecord kts = do
              -- FIXME
              -- _ <- loop ctx t
              case StrMapIsh.get field kts of
                Just ty -> pure ty
                Nothing -> errorSimple (_S::S_ "Missing field") $ field
            handleType kts = do
              case StrMapIsh.get field kts of
                Just ty -> pure $ AST.mkPi field ty $ term expr
                Nothing -> errorSimple (_S::S_ "Missing field") $ field
            casing = (\_ -> error unit)
              # VariantF.on (_S::S_ "Record") handleRecord
              # VariantF.on (_S::S_ "Const") \(Const.Const c) ->
                  case c of
                    Type -> term expr # Dhall.Core.normalize # AST.projectW #
                      VariantF.on (_S::S_ "Union") handleType (\_ -> error unit)
                    _ -> error unit
          tyR # Dhall.Core.normalize # AST.projectW # casing
      , "Project": \(Tuple (App ks) expr) -> do
          kts <- ensure (_S::S_ "Record") expr
            (errorSimple (_S::S_ "Cannot project"))
          -- FIXME
          -- _ <- loop ctx t
          AST.mkRecord <$> forWithIndex ks \k (_ :: Unit) ->
            StrMapIsh.get k kts #
              (noteSimple (_S::S_ "Missing field") k)
      , "ImportAlt": \(Pair l _r) ->
          -- FIXME???
          Dhall.Core.normalize <$> typecheck l
      , "Embed": onConst (pure <<< tpa)
      }
  in VariantF.onMatch contextual \v -> ReaderT \ctx ->
      VariantF.match preservative (map (hoistCofree (runReaderT <@> ctx)) v)

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

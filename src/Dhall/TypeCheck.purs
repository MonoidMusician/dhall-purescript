module Dhall.TypeCheck where

import Prelude

import Complex.Validation.These as V
import Control.Alternative (class Alternative)
import Control.Comonad (class Comonad, extract)
import Control.Comonad.Cofree (Cofree, hoistCofree)
import Control.Comonad.Cofree as Cofree
import Control.Comonad.Env (EnvT(..))
import Control.Monad.Reader (ReaderT(..), mapReaderT, runReaderT)
import Control.Monad.Writer (WriterT, mapWriterT)
import Control.Plus (empty)
import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Bifunctor (lmap)
import Data.Const as Const
import Data.Foldable (class Foldable, foldMap, for_, traverse_)
import Data.FoldableWithIndex (class FoldableWithIndex, foldMapWithIndex, forWithIndex_)
import Data.Function (on)
import Data.Functor.App (App(..))
import Data.Functor.Product (Product(..))
import Data.Functor.Variant (FProxy, SProxy)
import Data.Functor.Variant as VariantF
import Data.FunctorWithIndex (mapWithIndex)
import Data.Identity (Identity(..))
import Data.Lazy (Lazy)
import Data.List (List)
import Data.List as List
import Data.List.NonEmpty as NEL
import Data.List.Types (NonEmptyList)
import Data.Maybe (Maybe(..), maybe)
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
import Data.Traversable (class Traversable, traverse)
import Data.TraversableWithIndex (forWithIndex)
import Data.Tuple (Tuple(..), uncurry)
import Data.Variant (Variant)
import Data.Variant as Variant
import Dhall.Context (Context)
import Dhall.Context as Dhall.Context
import Dhall.Core as Dhall.Core
import Dhall.Core.AST (_S, S_, Const(..), Expr, ExprRowVFI(..), Pair(..))
import Dhall.Core.AST as AST
import Dhall.Core.StrMapIsh (class StrMapIsh)
import Dhall.Core.StrMapIsh as StrMapIsh
import Matryoshka (class Recursive, ana, project)
import Type.Row as R

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
  -- The explanation, given as text interspersed with specific places to look at
  -- (for the user to read)
  , explanation :: AST.TextLitF (Focus m a)
  -- The tag for the specific error, mostly for machine purposes
  , tag :: Variant r
  }

mapFocus :: forall r m a m' a'.
  (Focus m a -> Focus m' a') ->
  TypeCheckError r m a -> TypeCheckError r m' a'
mapFocus f (TypeCheckError e) = TypeCheckError $ e
  { location = f e.location
  , explanation = map f e.explanation
  }

errorSimple ::
  forall sym t r r' w m a b.
    IsSymbol sym =>
    R.Cons sym t r' r =>
  SProxy sym ->
  t ->
  Feedback w r m a b
errorSimple sym v = V.liftW $ V.erroring $ TypeCheckError
  { location: MainExpression
  , explanation: AST.TextLit ""
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
  , explanation: AST.TextLit ""
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

{-
recursor' :: forall t f m. Recursive t f => Functor m =>
  (f (Cofree m (Mu (Compose f (Cofree m)))) -> m t) -> t -> Cofree m (Mu (Compose f (Cofree m)))
recursor' f = go where
  go :: t -> Cofree m (Mu (Compose f (Cofree m)))
  go t = project t <#> go # ana do
    EnvT <<< ((embed <<< Compose) &&& (map (map go <<< project) <<< f))

recursor'' :: forall t f m. Recursive t f => Functor m =>
  (f (Cofree m t) -> m t) -> t -> Cofree m t
recursor'' f = go where
  go :: t -> Cofree m t
  go t = ana (EnvT <<< (identity &&& (f <<< map go <<< project))) t

recursor''' ::
  forall t f m r.
    Recursive t f =>
    Corecursive r (Compose (Cofree m) f) =>
    Traversable f =>
    Applicative m =>
  (f (Cofree m r) -> m t) -> t -> Cofree m r
recursor''' f = go where
  go :: t -> Cofree m r
  go t = embed $ EnvT $ project t # map go # (&&&)
    do embed <<< Compose <<< distGHisto distApplicative
    do map go <<< f

recursor''''' ::
  forall t f m r.
    Recursive t f =>
    Corecursive r (Compose (Cofree m) f) =>
    Traversable f =>
    Applicative m =>
  (f (Cofree m r) -> m t) -> t -> Cofree m r
recursor''''' f = go where
  go :: t -> Cofree m r
  go = buildCofree \t ->
    project t <#> go # flip (&&&) f do
      embed <<< Compose <<< buildCofree do
        map extract &&& traverse Cofree.tail

recursor'''' ::
  forall t f m r.
    Recursive t f =>
    Traversable f =>
    Corecursive r (Compose (Cofree m) f) =>
    Applicative m =>
  (f (Cofree m r) -> m t) -> t -> Cofree m r
recursor'''' f = go where
  go :: t -> Cofree m r
  go t = t # transAna do
    EnvT <<< do
      map go >>> do
        (distGHisto distApplicative >>> Compose >>> embed) &&& f

terms :: forall m f. Functor f => Functor m => Mu (Compose f (Cofree m)) -> Mu f
terms = transMu (un Compose >>> map extract)

typecheck_terms :: forall m f. Functor f => Functor m => Mu (Compose f (Cofree m)) -> m (Mu f)
typecheck_terms = Cofree.tail >>> map terms
-}

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

type Errors r m a =
  ( "Not a function" :: Unit
  , "Type mismatch" :: { function :: Expr m a
                       , expected :: Expr m a
                       , argument :: Expr m a
                       , actual :: Expr m a
                       }
  , "Invalid predicate" :: Unit
  , "If branch mismatch" :: Unit
  , "If branch must be term" :: Tuple Boolean Unit
  , "Invalid list type" :: Unit
  , "Missing list type" :: Unit
  , "Invalid list element" :: Int
  , "Mismatched list elements" :: Int
  , "Cannot append non-list" :: Tuple Boolean Unit
  , "Cannot interpolate" :: Tuple Natural Unit
  , "List append mistmatch" :: Unit
  , "Invalid optional type" :: Unit
  , "Invalid optional element" :: Unit
  , "Invalid `Some`" :: Unit
  , "Duplicate record fields" :: NonEmptyList String
  , "Invalid field type" :: Tuple String Unit
  , "Inconsistent field types" :: Inconsistency
                                    (NonEmptyList
                                       { key :: String
                                       , value :: { kind :: Const
                                                  , ty :: Expr m a
                                                  }
                                       }
                                    )
  , "Duplicate union fields" :: NonEmptyList String
  , "Invalid alternative type" :: Tuple String Unit
  , "Must combine a record" :: Tuple Boolean Unit
  , "Record mismatch" :: Unit
  , "Oops" :: Unit
  , "Must merge a record" :: Unit
  , "Must merge a union" :: Unit
  , "Missing merge type" :: Unit
  , "Handler not a function" :: Unit
  , "Dependent handler function" :: Unit
  , "Missing handler" :: Set Unit
  , "Handler input type mismatch" :: Unit
  , "Unused handlers" :: Set Unit
  , "Cannot project" :: Unit
  , "Missing field" :: String
  , "Invalid input type" :: Unit
  , "Invalid output type" :: Unit
  , "No dependent types" :: Tuple (Expr m a) (Expr m a)
  , "Unbound variable" :: AST.Var
  , "Annotation mismatch" :: Unit
  , "`Kind` has no type" :: Unit
  , "Expected type" :: { expected :: Expr m a
                       , received :: Expr m a
                       }
  , "Cannot access" :: String
  , "Constructors requires a union type" :: Unit
  | r
  )
type FeedbackE w r m a = WriterT (Array (Variant w)) (V.Erroring (TypeCheckError (Errors r m a) m a))
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
              oblivious <<< noteSimple (_S::S_ "No dependent types") (Tuple (term ty) (term ty_body))
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
              oblivious <<< noteSimple (_S::S_ "No dependent types") (Tuple (term ty) (term ty_body))
      , "Let": \(AST.LetF name mty value expr) -> do
          ty <- Cofree.tail value
          for_ mty \ty' -> do
            _ <- typecheck ty'
            if Dhall.Core.judgmentallyEqual (term ty) (term ty') then pure unit else
              oblivious <<< errorSimple (_S::S_ "Annotation mismatch") $ unit
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
        checkBinOp t p = suggest t $ for_ p $
          -- t should be simple enough that alphaNormalize is unnecessary
          \operand -> typecheck operand >>= Dhall.Core.normalize >>> case _ of
            ty_operand | t == ty_operand -> pure unit
              | otherwise -> errorSimple
                (_S::S_ "Expected type") { expected: t, received: t }

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
                  let nf_aty0 = Dhall.Core.normalize aty0
                  let nf_aty1 = Dhall.Core.normalize aty1
                  -- SPECIAL!
                  -- Recovery case: if the variable is free in the return type
                  -- then this is a non-dependent function
                  -- and its return type can be suggested
                  -- even if its argument does not have the right type
                  (if not Dhall.Core.freeIn name0 rty then suggest rty else identity) $
                    errorSimple (_S::S_ "Type mismatch")
                      { function: term f
                      , expected: nf_aty0
                      , argument: term a
                      , actual: nf_aty1
                      }
          in join $ checkArg <$> checkFn <*> typecheck a
      , "Annot": \(AST.Pair expr ty) ->
          let
            checkEq aty0 aty1 =
              if Dhall.Core.judgmentallyEqual aty0 aty1 then pure aty0 else
                errorSimple (_S::S_ "Annotation mismatch") $ unit
          in join $ checkEq <$> typecheck expr <*> (term ty <$ typecheck ty)
      , "Bool": identity aType
      , "BoolLit": always $ AST.mkBool
      , "BoolAnd": checkBinOp AST.mkBool
      , "BoolOr": checkBinOp AST.mkBool
      , "BoolEQ": checkBinOp AST.mkBool
      , "BoolNE": checkBinOp AST.mkBool
      , "BoolIf": \(AST.Triplet c t f) ->
          ensure (_S::S_ "Bool") c
            (errorSimple (_S::S_ "Invalid predicate")) *>
          let
            checkMatch ty_t ty_f =
              if Dhall.Core.judgmentallyEqual ty_t ty_f then pure ty_t else
                errorSimple (_S::S_ "If branch mismatch") $ unit
          in join $ checkMatch
              <$> ensureTerm t
                (errorSimple (_S::S_ "If branch must be term") <<< Tuple false)
              <*> ensureTerm f
                (errorSimple (_S::S_ "If branch must be term") <<< Tuple true)
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
            (errorSimple (_S::S_ "Cannot interpolate") <<< Tuple i)
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
            if Dhall.Core.judgmentallyEqual ty ty' then pure unit else
              case mty of
                Nothing ->
                  errorSimple (_S::S_ "Invalid list element") $ i
                Just _ ->
                  errorSimple (_S::S_ "Mismatched list elements") $ i
      , "ListAppend": \p -> AST.mkApp AST.mkList <$> do
          AST.Pair ty_l ty_r <- forWithIndex p \side expr -> do
            let error = errorSimple (_S::S_ "Cannot append non-list") <<< Tuple side
            expr_ty <- typecheck expr
            AST.Pair list ty <- ensure' (_S::S_ "App") expr_ty error
            Dhall.Core.normalize list # AST.projectW #
              VariantF.on (_S::S_ "List") (const (pure unit))
                \_ -> absurd <$> error unit
            pure ty
          if Dhall.Core.judgmentallyEqual ty_l ty_r then pure ty_l else
            errorSimple (_S::S_ "List append mistmatch") $ unit
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
              ty' <- typecheck expr
              if Dhall.Core.judgmentallyEqual (term ty) ty' then pure unit else
                errorSimple (_S::S_ "Invalid optional element") $ unit
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
                (errorSimple (_S::S_ "Invalid field type") <<< Tuple field)
              case c of
                Kind | not Dhall.Core.judgmentallyEqual AST.mkType (term ty) ->
                  (errorSimple (_S::S_ "Invalid field type") <<< Tuple field) $ unit
                _ -> pure unit
              pure { kind: c, ty: term ty }
            ensureConsistency (eq `on` _.kind)
              (errorSimple (_S::S_ "Inconsistent field types")) kts'
            pure $ AST.mkConst $ maybe Type _.kind $ un First $ foldMap pure kts'
      , "RecordLit": \kvs ->
          ensureNodupes
            (errorSimple (_S::S_ "Duplicate record fields")) kvs
          *> do
            kts <- traverse Cofree.tail kvs
            suggest (AST.mkRecord (term <$> kts)) do
              kts' <- forWithIndex kts \field ty -> do
                c <- unwrap <$> ensure (_S::S_ "Const") ty
                  (errorSimple (_S::S_ "Invalid field type") <<< Tuple field)
                case c of
                  Kind | not Dhall.Core.judgmentallyEqual AST.mkType (term ty) ->
                    (errorSimple (_S::S_ "Invalid field type") <<< Tuple field) $ unit
                  _ -> pure unit
                pure { kind: c, ty: term ty }
              ensureConsistency (eq `on` _.kind)
                (errorSimple (_S::S_ "Inconsistent field types")) kts'
      , "Union": \kts ->
          ensureNodupes
            (errorSimple (_S::S_ "Duplicate union fields")) kts
          *> do
            -- FIXME: should this be the largest of `Type` or `Kind` returned?
            suggest AST.mkType $
              forWithIndex_ kts \field ty -> do
                void $ ensure (_S::S_ "Const") ty
                  (errorSimple (_S::S_ "Invalid alternative type") <<< Tuple field)
      , "UnionLit": \(Product (Tuple (Tuple field expr) kts)) ->
          ensureNodupes
            (errorSimple (_S::S_ "Duplicate union fields")) kts
          *> do
            ty <- Cofree.tail expr
            let kts' = StrMapIsh.insert field ty kts
            forWithIndex_ kts' \field' kind -> do
              void $ ensure (_S::S_ "Const") kind
                (errorSimple (_S::S_ "Invalid alternative type") <<< Tuple field')
            pure $ AST.mkUnion $ term <$> kts'
      , "Combine": \p -> do
          AST.Pair { const: constL, kts: ktsL } { const: constR, kts: ktsR } <-
            forWithIndex p \side ty -> do
              kalls <- { ty: _, kind: _ } <$> typecheck ty <*> kindcheck ty
              kts <- ensure' (_S::S_ "Record") kalls.ty
                (errorSimple (_S::S_ "Must combine a record") <<< Tuple side)
              const <- unwrap <$> ensure' (_S::S_ "Const") kalls.kind
                (errorSimple (_S::S_ "Must combine a record") <<< Tuple side)
              pure { kts, const }
          -- kind checking only needs to occur at the top level
          -- since nested records will have the same (compatible) kinds
          when (constL /= constR) $ errorSimple (_S::S_ "Record mismatch") unit
          let
            combineTypes (p' :: Pair (Expr m a)) = do
              AST.Pair ktsL' ktsR' <-
                forWithIndex p' \side ty -> do
                  ensure' (_S::S_ "Record") ty
                    (errorSimple (_S::S_ "Must combine a record") <<< Tuple side)
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
              kalls <- { ty: _, kind: _ } <$> typecheck ty <*> kindcheck ty
              kts <- ensure' (_S::S_ "Record") kalls.ty
                (errorSimple (_S::S_ "Must combine a record") <<< Tuple side)
              const <- unwrap <$> ensure' (_S::S_ "Const") kalls.kind
                (errorSimple (_S::S_ "Must combine a record") <<< Tuple side)
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
                      (errorSimple (_S::S_ "Must combine a record") <<< Tuple side)
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
      , "Prefer": \p -> do
          AST.Pair { const: constL, kts: ktsL } { const: constR, kts: ktsR } <-
            forWithIndex p \side kvs -> do
              ty <- Cofree.tail kvs
              kts <- ensure' (_S::S_ "Record") (term ty)
                (errorSimple (_S::S_ "Must combine a record") <<< Tuple side)
              const <- unwrap <$> ensure (_S::S_ "Const") ty
                (errorSimple (_S::S_ "Must combine a record") <<< Tuple side)
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
            Nothing -> case un First $ foldMap pure ktsX of
              Nothing -> errorSimple (_S::S_ "Missing merge type") $ unit
              Just item -> do
                AST.BindingBody name _ output <- ensure' (_S::S_ "Pi") item
                  (errorSimple (_S::S_ "Handler not a function"))
                -- NOTE: the following check added
                when (Dhall.Core.freeIn (AST.V name 0) output)
                  (errorSimple (_S::S_ "Dependent handler function") unit)
                pure $ Dhall.Core.shift (-1) (AST.V name 0) output
          forWithIndex_ ktsY \k tY -> do
            tX <- StrMapIsh.get k ktsX #
              noteSimple (_S::S_ "Missing handler") diffX
            AST.BindingBody name input output <- ensure' (_S::S_ "Pi") tX
              (errorSimple (_S::S_ "Handler not a function"))
            ado
              when (not Dhall.Core.judgmentallyEqual tY input)
                (errorSimple (_S::S_ "Handler input type mismatch") unit)
            in do
              -- NOTE: the following check added
              when (Dhall.Core.freeIn (AST.V name 0) output)
                (errorSimple (_S::S_ "Dependent handler function") unit)
              let output' = Dhall.Core.shift (-1) (AST.V name 0) output
              when (not Dhall.Core.judgmentallyEqual ty output')
                (errorSimple (_S::S_ "Handler output type mismatch") unit)
          pure ty <*
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

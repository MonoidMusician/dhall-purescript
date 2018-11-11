module Dhall.TypeCheck where

import Prelude

import Complex.Validation.These as V
import Control.Alternative (class Alternative)
import Control.Comonad (class Comonad, extract)
import Control.Comonad.Cofree (Cofree, hoistCofree)
import Control.Comonad.Cofree as Cofree
import Control.Monad.Reader (ReaderT(..), runReaderT)
import Control.Monad.Writer (WriterT(..))
import Control.Plus (empty)
import Data.Array as Array
import Data.Bifunctor (lmap)
import Data.Const as Const
import Data.Const as ConstF
import Data.Either (Either(..))
import Data.Foldable (foldMap, for_)
import Data.FoldableWithIndex (forWithIndex_, traverseWithIndex_)
import Data.Functor.Product (Product(..))
import Data.Functor.Variant (FProxy(..), SProxy(..))
import Data.Functor.Variant as VariantF
import Data.FunctorWithIndex (class FunctorWithIndex, mapWithIndex)
import Data.Identity (Identity(..))
import Data.List (List)
import Data.Maybe (Maybe(..))
import Data.Newtype (un, unwrap, wrap)
import Data.Profunctor.Strong ((&&&))
import Data.Symbol (class IsSymbol)
import Data.Traversable (class Traversable, for)
import Data.TraversableWithIndex (forWithIndex)
import Data.Tuple (Tuple(..), fst)
import Data.Variant (Variant)
import Data.Variant as Variant
import Dhall.Context (Context(..))
import Dhall.Context as Dhall.Context
import Dhall.Core (S_, _s, denote)
import Dhall.Core as Dhall.Core
import Dhall.Core.AST (Const(..), Expr(..), Pair(..))
import Dhall.Core.AST as AST
import Dhall.Core.StrMapIsh (class StrMapIsh)
import Dhall.Core.StrMapIsh as StrMapIsh
import Matryoshka (class Recursive, project)
import Matryoshka as Matryoshka
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
type Typer m a = forall s. a -> Expr m s a

suggest :: forall w r m s a x y. x -> Feedback w r m s a y -> Feedback w r m s a x
suggest a = (<<<) wrap $ unwrap >>> case _ of
  V.Success (Tuple _ accum) ->
    V.Success (Tuple a accum)
  V.Error es mtaccum ->
    V.Error es $ pure $ Tuple a $ foldMap extract mtaccum

newtype TypeCheckError r m s a = TypeCheckError
  -- The main location where the typechecking error occurred
  { location :: List (AST.ExprRowVFI s a)
  -- The explanation, given as text interspersed with specific places to look at
  -- (for the user to read)
  , explanation :: AST.TextLitF (Focus m s a)
  -- The tag for the specific error, mostly for machine purposes
  , tag :: Variant r
  }

errorSimple ::
  forall sym t r r' w m s a b.
    IsSymbol sym =>
    R.Cons sym t r' r =>
  SProxy sym ->
  t ->
  Feedback w r m s a b
errorSimple sym v = V.liftW $ V.erroring $ TypeCheckError
  { location: empty
  , explanation: AST.TextLit ""
  , tag: Variant.inj sym v
  }

noteSimple ::
  forall sym t r r' w m s a b.
    IsSymbol sym =>
    R.Cons sym t r' r =>
  SProxy sym ->
  t ->
  Maybe b ->
  Feedback w r m s a b
noteSimple sym v = (<<<) V.liftW $ V.note $ TypeCheckError
  { location: empty
  , explanation: AST.TextLit ""
  , tag: Variant.inj sym v
  }

-- An expression for the user to look at when an error occurs, giving
-- specific context for what went wrong.
data Focus m s a
  -- Atomic: Pointer to a focus in the original tree
  = ExistingFocus (List (AST.ExprRowVFI s a))
  -- Derived: Point to the type of another focus
  | TypeOfFocus (Focus m s a)
  -- Atomic: A new expression, whose origin is shrouded in mystery ...
  | ConstructedFocus (Expr m s a)

type Ctx m s a = Context (Expr m s a)
type Feedback w r m s a = WriterT (Array (Variant w)) (V.Erroring (TypeCheckError r m s a))
type CtxFeedback w r m s a = ReaderT (Ctx m s a) (Feedback w r m s a)
type TypeChecked w r m s a = Feedback w r m s a (Expr m s a)
type CtxTypeChecked w r m s a = CtxFeedback w r m s a (Expr m s a)
type Shallot w r m s a = Cofree (Feedback w r m s a) (Expr m s a)
-- A shallot only has one context for the term, type, and kind
type CtxShallot w r m s a = Cofree (ReaderT (Ctx m s a) (Feedback w r m s a)) (Expr m s a)

-- This is `lift` for `ReaderT`, without the (`Monad`) constraints.
oblivious :: forall w r m s a. Feedback w r m s a ~> CtxFeedback w r m s a
oblivious = ReaderT <<< const

-- This is the proper way to introduce a type into the context.
intro :: forall w r m s a. StrMapIsh m => Eq a => String -> CtxShallot w r m s a -> Ctx m s a -> Ctx m s a
intro name ty ctx =
  Dhall.Core.shift 1 (AST.V name 0) <$>
    Dhall.Context.insert name (Dhall.Core.normalize (extract ty)) ctx

-- This is `local` for `ReaderT`, without the (`Monad`) constraints.
localize :: forall w r m s a. (Ctx m s a -> Ctx m s a) -> CtxFeedback w r m s a ~> CtxFeedback w r m s a
localize f act = ReaderT $ f >>> runReaderT act

introize :: forall w r m s a. StrMapIsh m => Eq a => String -> CtxShallot w r m s a -> CtxFeedback w r m s a ~> CtxFeedback w r m s a
introize name ty = localize (intro name ty)

-- This is a weird kind of catamorphism that lazily gives access to
-- (potentially infinite) applications of itself to its output.
-- `para` on steroids.
recursor :: forall t f m. Recursive t f => Functor m =>
  (f (Cofree m t) -> m t) -> t -> m t
recursor f = go where
  go :: t -> m t
  go e = project e <#> Cofree.buildCofree (identity &&& go) # f

-- typecheck :: forall w r m s a. Shallot w r m s a -> TypeChecked w r m s a
-- typecheck :: forall w r m s a. CtxShallot w r m s a -> CtxTypeChecked w r m s a
typecheck :: forall f a. Functor f => Cofree f a -> f a
typecheck s = Cofree.tail s <#> extract

-- kindcheck :: forall w r m s a. Shallot w r m s a -> TypeChecked w r m s a
-- kindcheck :: forall w r m s a. CtxShallot w r m s a -> CtxTypeChecked w r m s a
kindcheck :: forall f a. Bind f => Cofree f a -> f a
kindcheck s = Cofree.tail s >>= typecheck

-- term :: forall w r m s a. Shallot w r m s a -> Expr m s a
-- term :: forall w r m s a. CtxShallot w r m s a -> Expr m s a
term :: forall m a. Comonad m => m a -> a
term = extract

{-| Generalization of `typeWith` that allows type-checking the `Embed`
    constructor with custom logic
-}
typeWithA :: forall m s a.
  Eq a => StrMapIsh m =>
  Typer m a ->
  Context (Expr m s a) ->
  Expr m s a ->
  TypeChecked _ _ m s a
typeWithA tpa = flip $ compose runReaderT $ recursor $
  let
    -- Tag each error/warning with the index at which it occurred, recursively
    indexFeedback = identity
    -- mapWithIndex (map <<< map <<< V.scoped (_s::S_ "Within"))
  in
  -- Before we pass it to the handler below, tag indices and then unwrap it
  (>>>) indexFeedback $
  (>>>) unwrap $
  let
    ensure' :: forall sym f r'.
      IsSymbol sym =>
      R.Cons sym (FProxy f) r' (AST.ExprLayerRow m s a) =>
      SProxy sym ->
      Expr m s a ->
      (Unit -> Feedback _ _ m s a Void) ->
      Feedback _ _ m s a (f (Expr m s a))
    ensure' s ty error =
      let nf_ty = Dhall.Core.normalize ty in
      AST.projectW nf_ty # VariantF.on s pure
        \_ -> absurd <$> error unit

  in let
    contextual =
      let
        ensureConst_ctx ::
          CtxShallot _ _ m s a ->
          (Unit -> Feedback _ _ m s a Void) ->
          CtxFeedback _ _ m s a Const
        ensureConst_ctx expr error = do
          ty <- typecheck expr
          oblivious $ unwrap <$> ensure' (_s::S_ "Const") ty error
      in
      { "Const": unwrap >>> \c ->
          axiom c <#> AST.mkConst #
            oblivious <<< noteSimple (_s::S_ "`Kind` has no type") unit
      , "Var": unwrap >>> \v@(AST.V name idx) -> ReaderT \ctx ->
          Dhall.Context.lookup name idx ctx #
            noteSimple (_s::S_ "Unbound variable") v
      , "Lam": \(AST.BindingBody name ty body) -> do
          kA <- ensureConst_ctx ty
            (errorSimple (_s::S_ "Invalid input type"))
          -- normalize (as part of `intro`) _after_ typechecking succeeds
          -- (in order to guarantee that normalization terminates)
          introize name ty do
            ty_body <- Cofree.tail body
            kB <- ensureConst_ctx ty_body
              (errorSimple (_s::S_ "Invalid output type"))
            _ <- rule kA kB #
              oblivious <<< noteSimple (_s::S_ "No dependent types") (Tuple (term ty) (term ty_body))
            pure $ AST.mkPi name (term ty) (term ty_body)
      , "Pi": \(AST.BindingBody name ty ty_body) -> do
          kA <- ensureConst_ctx ty
            (errorSimple (_s::S_ "Invalid input type"))
          -- normalize (as part of `intro`) _after_ typechecking succeeds
          -- (in order to guarantee that normalization terminates)
          introize name ty do
            kB <- ensureConst_ctx ty_body
              (errorSimple (_s::S_ "Invalid output type"))
            map AST.mkConst $ rule kA kB #
              oblivious <<< noteSimple (_s::S_ "No dependent types") (Tuple (term ty) (term ty_body))
      , "Let": \(AST.LetF name mty value expr) -> do
          ty <- Cofree.tail value
          for_ mty \ty' -> do
            _ <- typecheck ty'
            if Dhall.Core.judgmentallyEqual (term ty) (term ty') then pure unit else
              oblivious <<< errorSimple (_s::S_ "Annotation mismatch") $ unit
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
              introize name ty $ fallback unit
            handleType _ = fallback unit

            fallback _ =
              typecheck expr <#> substShiftOut
          kind # Dhall.Core.normalize # AST.projectW #
            VariantF.on (_s::S_ "Const")
              (unwrap >>> handleType)
              \_ -> fallback unit
      }
    preservative =
      let
        onConst :: forall x.
          (x -> Feedback _ _ m s a (Expr m s a)) ->
          Const.Const x (Shallot _ _ m s a) ->
          TypeChecked _ _ m s a
        onConst f (Const.Const c) = f c
        always :: forall x y. x -> y -> Feedback _ _ m s a x
        always b _ = pure b
        aType :: forall x. Const.Const x (Shallot _ _ m s a) -> TypeChecked _ _ m s a
        aType = always $ AST.mkType
        aFunctor :: forall x. Const.Const x (Shallot _ _ m s a) -> TypeChecked _ _ m s a
        aFunctor = always $ AST.mkArrow AST.mkType AST.mkType
        a0 = AST.mkVar (AST.V "a" 0)

        -- TODO: This will need to become aware of AST holes
        -- Check a binary operation (`Pair` functor) against a simple, static,
        -- *normalized* type `t`.
        checkBinOp ::
          Expr m Void a ->
          Pair (Shallot _ _ m s a) ->
          TypeChecked _ _ m s a
        checkBinOp t p = suggest (lmap absurd t) $ for_ p $
          -- t should be simple enough that alphaNormalize is unnecessary
          \operand -> typecheck operand >>= Dhall.Core.normalize >>> case _ of
            ty_operand | t == ty_operand -> pure unit
              | otherwise -> errorSimple
                (_s::S_ "Expected type") { expected: t, received: t }

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
          R.Cons sym (FProxy f) r' (AST.ExprLayerRow m s a) =>
          SProxy sym ->
          Shallot _ _ m s a ->
          (Unit -> Feedback _ _ m s a Void) ->
          Feedback _ _ m s a (f (Expr m s a))
        ensure s expr error = do
          ty <- typecheck expr
          ensure' s ty error

        -- Ensure that the passed `expr` is a term; i.e. the type of its type
        -- is `Type`. Returns the type of the `expr`.
        ensureTerm ::
          Shallot _ _ m s a ->
          (Unit -> Feedback _ _ m s a Void) ->
          Feedback _ _ m s a (Expr m s a)
        ensureTerm expr error = do
          ty <- Cofree.tail expr
          term ty <$ ensureType ty error

        -- Ensure that the passed `ty` is a type; i.e. its type is `Type`.
        ensureType ::
          Shallot _ _ m s a ->
          (Unit -> Feedback _ _ m s a Void) ->
          Feedback _ _ m s a Unit
        ensureType ty error = do
          kind <- typecheck ty
          ensure' (_s::S_ "Const") kind error >>= case _ of
            Const.Const Type -> pure unit
            _ -> absurd <$> error unit
      in
      { "App": \(AST.Pair f a) ->
          let
            checkFn = ensure (_s::S_ "Pi") f
              (errorSimple (_s::S_ "Not a function"))
            checkArg (AST.BindingBody name aty0 rty) aty1 =
              let name0 = AST.V name 0 in
              if Dhall.Core.judgmentallyEqual aty0 aty1
                then do
                  -- TODO: abstract this out
                  let a'    = Dhall.Core.shift   1  name0 (term a)
                  let rty'  = Dhall.Core.subst      name0 a' rty
                  let rty'' = Dhall.Core.shift (-1) name0    rty'
                  pure rty''
                else do
                  let nf_aty0 = Dhall.Core.normalize aty0
                  let nf_aty1 = Dhall.Core.normalize aty1
                  -- SPECIAL!
                  -- Recovery case: if the variable is free in the return type
                  -- then this is a non-dependent function
                  -- and its return type can be suggested
                  -- even if its argument does not have the right type
                  (if Dhall.Core.freeIn name0 rty then suggest rty else identity) $
                    errorSimple (_s::S_ "Type mismatch")
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
                errorSimple (_s::S_ "Annotation mismatch") $ unit
          in join $ checkEq <$> typecheck expr <*> (term ty <$ typecheck ty)
      , "Bool": identity aType
      , "BoolLit": always $ AST.mkBool
      , "BoolAnd": checkBinOp AST.mkBool
      , "BoolOr": checkBinOp AST.mkBool
      , "BoolEQ": checkBinOp AST.mkBool
      , "BoolNE": checkBinOp AST.mkBool
      , "BoolIf": \(AST.Triplet c t f) ->
          ensure (_s::S_ "Bool") c
            (errorSimple (_s::S_ "Invalid predicate")) *>
          let
            checkMatch ty_t ty_f =
              if Dhall.Core.judgmentallyEqual ty_t ty_f then pure ty_t else
                errorSimple (_s::S_ "If branch mismatch") $ unit
          in join $ checkMatch
              <$> ensureTerm t
                (errorSimple (_s::S_ "If branch must be term") <<< Tuple false)
              <*> ensureTerm f
                (errorSimple (_s::S_ "If branch must be term") <<< Tuple true)
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
      , "TextLit": always $ AST.mkText
      , "TextAppend": checkBinOp AST.mkText
      , "List": identity aFunctor
      , "ListLit": \(Product (Tuple mty lit)) -> AST.mkApp AST.mkList <$> do
          -- get the assumed type of the list
          (ty :: Expr m s a) <- case mty of
            -- either from annotation
            Just ty -> suggest (term ty) $
              ensureType ty
                (errorSimple (_s::S_ "Invalid list type"))
            -- or from the first element
            Nothing -> case Array.head lit of
              Nothing -> errorSimple (_s::S_ "Missing list type") $ unit
              Just item0 -> do
                ensureTerm item0
                  (errorSimple (_s::S_ "Invalid list type"))
          suggest ty $ forWithIndex_ lit \i item -> do
            ty' <- typecheck item
            if Dhall.Core.judgmentallyEqual ty ty' then pure unit else
              case mty of
                Nothing ->
                  errorSimple (_s::S_ "Invalid list element") $ i
                Just _ ->
                  errorSimple (_s::S_ "Mismatched list elements") $ i
      , "ListAppend": \p -> AST.mkApp AST.mkList <$> do
          AST.Pair ty_l ty_r <- forWithIndex p \side expr -> do
            let error = errorSimple (_s::S_ "Cannot append non-list") <<< Tuple side
            expr_ty <- typecheck expr
            AST.Pair list ty <- ensure' (_s::S_ "App") expr_ty error
            Dhall.Core.normalize list # AST.projectW #
              VariantF.on (_s::S_ "List") (const (pure unit))
                \_ -> absurd <$> error unit
            pure ty
          if Dhall.Core.judgmentallyEqual ty_l ty_r then pure ty_l else
            errorSimple (_s::S_ "List append mistmatch") $ unit
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
            (errorSimple (_s::S_ "Invalid optional type"))
          suggest (AST.mkApp AST.mkOptional (term ty)) $
            for_ mexpr \expr -> do
              ty' <- typecheck expr
              if Dhall.Core.judgmentallyEqual (term ty) ty' then pure unit else
                errorSimple (_s::S_ "Invalid optional element") $ unit
      , "Some": unwrap >>> \a ->
          AST.mkApp AST.mkOptional <$> ensureTerm a
            (errorSimple (_s::S_ "Invalid `Some`"))
      , "OptionalFold": always $ AST.mkForall "a" $
          AST.mkArrow (AST.mkApp AST.mkOptional a0) (optionalEnc a0)
      , "OptionalBuild": always $ AST.mkForall "a" $
          AST.mkArrow (optionalEnc a0) (AST.mkApp AST.mkOptional a0)
      , "Record": ?help
      , "RecordLit": ?help
      , "Union": \kts ->
          -- FIXME: should this be the largest of `Type` or `Kind` returned?
          suggest AST.mkType $
            forWithIndex_ kts \field ty -> do
              void $ ensure (_s::S_ "Const") ty
                (errorSimple (_s::S_ "Invalid alternative type") <<< Tuple field)
      , "UnionLit": \(Product (Tuple (Tuple field expr) kts)) -> do
          ty <- Cofree.tail expr
          let kts' = StrMapIsh.insert field ty kts
          forWithIndex_ kts' \field kind -> do
            void $ ensure (_s::S_ "Const") kind
              (errorSimple (_s::S_ "Invalid alternative type") <<< Tuple field)
          pure $ AST.mkUnion $ term <$> kts'
      , "Combine": ?help
      , "CombineTypes": ?help
      , "Prefer": ?help
      , "Merge": ?help
      , "Constructors": \(Identity ty) -> do
          void $ typecheck ty
          kts <- term ty # Dhall.Core.normalize # AST.projectW #
            VariantF.on (_s::S_ "Union") pure
              \_ -> errorSimple (_s::S_ "Constructors requires a union type") $ unit
          pure $ AST.mkRecord $ kts # mapWithIndex \field ty' ->
            AST.mkPi field ty' $ term ty
      , "Field": \(Tuple field expr) -> do
          ty <- typecheck expr
          let
            error _ = errorSimple (_s::S_ "Cannot access") $ field
            handleRecord kts = do
              -- FIXME
              -- _ <- loop ctx t
              case StrMapIsh.get field kts of
                Just ty -> pure ty
                Nothing -> errorSimple (_s::S_ "Missing field") $ field
            handleType kts = do
              case StrMapIsh.get field kts of
                Just ty -> pure $ AST.mkPi field ty $ term expr
                Nothing -> errorSimple (_s::S_ "Missing field") $ field
            casing = (\_ -> error unit)
              # VariantF.on (_s::S_ "Record") handleRecord
              # VariantF.on (_s::S_ "Const") \(Const.Const c) ->
                  case c of
                    Type -> term expr # Dhall.Core.normalize # AST.projectW #
                      VariantF.on (_s::S_ "Union") handleType (\_ -> error unit)
                    _ -> error unit
          ty # Dhall.Core.normalize # AST.projectW # casing
      , "Project": \(Tuple ks expr) -> do
          kts <- ensure (_s::S_ "Record") expr
            (errorSimple (_s::S_ "Cannot project"))
          -- FIXME
          -- _ <- loop ctx t
          AST.mkRecord <$> forWithIndex ks \k (_ :: Unit) ->
            StrMapIsh.get k kts #
              (noteSimple (_s::S_ "Missing field") k)
      , "Note": typecheck <<< extract
      , "ImportAlt": \(Pair l _r) ->
          -- FIXME???
          Dhall.Core.normalize <$> typecheck l
      , "Embed": onConst (pure <<< denote <<< tpa)
      }
  in VariantF.onMatch contextual \v -> ReaderT \ctx ->
      VariantF.match preservative (map (hoistCofree (runReaderT <@> ctx)) v :: VariantF.VariantF _ (Shallot _ _ m s a))

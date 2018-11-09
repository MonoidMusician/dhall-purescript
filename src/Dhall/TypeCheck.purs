module Dhall.TypeCheck where

import Prelude

import Complex.Validation.These as V
import Control.Alternative (class Alternative)
import Control.Comonad (extract)
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
import Data.Profunctor.Strong (fanout)
import Data.Symbol (class IsSymbol)
import Data.Traversable (for)
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
import Matryoshka (class Recursive, cata, para, project)
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

suggest :: forall ws es a b. a -> V.FeedbackR ws es b -> V.FeedbackR ws es a
suggest a = unwrap >>> case _ of
  V.Success (Tuple _ accum) ->
    wrap $ V.Success (Tuple a accum)
  V.Error es mtaccum ->
    wrap $ V.Error es $ pure $ Tuple a $
      -- preserve warnings, if any
      foldMap extract mtaccum

data TypeCheckError r m s a = TypeCheckError
  -- The main location where the typechecking error occurred
  { location :: List (AST.ExprRowVFI s a)
  -- The explanation, given as text interspersed with specific places to look at
  -- (for the user to read)
  , explanation :: AST.TextLitF (Focus m s a)
  -- The tag for the specific error, mostly for machine purposes
  , tag :: Variant r
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
type Feedback r m s a = V.Erroring (TypeCheckError r m s a)
type TypeChecked r m s a = Feedback r m s a (Expr m s a)
type TypeCheckedCtx r m s a = Ctx m s a -> TypeChecked r m s a

type Shallot r m s a =
  { the_term :: Expr m s a
  , its_type :: Feedback r m s a
    { the_type :: Expr m s a
    , its_kind :: TypeChecked r m s a
    }
  }

typechecked :: forall r m s a. Shallot r m s a -> TypeChecked r m s a
typechecked = _.its_type >>> map _.the_type

kindchecked :: forall r m s a. Shallot r m s a -> TypeChecked r m s a
kindchecked = _.its_type >>> (=<<) _.its_kind

type Fb ws es m s a = V.FeedbackR ws es (Expr m s a)
type CtxFb ws es m s a = Context (Expr m s a) -> Fb ws es m s a
type OnionCtx ws es m s a = Tuple (Expr m s a) (CtxFb ws es m s a)
type Onion ws es m s a = Tuple (Expr m s a) (Fb ws es m s a)

{-| Generalization of `typeWith` that allows type-checking the `Embed`
    constructor with custom logic
-}
typeWithA :: forall m s a.
  Eq a => StrMapIsh m =>
  Typer m a ->
  Context (Expr m s a) ->
  Expr m s a ->
  V.FeedbackR _ _ (Expr m s a)
typeWithA tpa = flip $ para $
  let
    -- Tag each error/warning with the index at which it occurred, recursively
    indexFeedback = mapWithIndex
      (map <<< map <<< V.scoped (_s::S_ "Within"))
  in
  -- Before we pass it to the handler below, tag indices and then unwrap it
  (>>>) indexFeedback $ (>>>) unwrap $
  let
    caramelize :: Expr m s a -> OnionCtx _ _ m s a
    caramelize = fanout identity $ flip $ typeWithA tpa

    ensure' :: forall sym f r'.
      IsSymbol sym =>
      R.Cons sym (FProxy f) r' (AST.ExprLayerRow m s a) =>
      SProxy sym ->
      Expr m s a ->
      (Unit -> V.FeedbackR _ _ Void) ->
      V.FeedbackR _ _ (f (Expr m s a))
    ensure' s ty error =
      let nf_ty = Dhall.Core.normalize ty in
      AST.projectW nf_ty # VariantF.on s pure
        \_ -> absurd <$> error unit

  in let
    contextual =
      let
        ensureConst_ctx ::
          OnionCtx _ _ m s a ->
          Context (Expr m s a) ->
          (Unit -> V.FeedbackR _ _ Void) ->
          V.FeedbackR _ _ Const
        ensureConst_ctx expr ctx error = do
          ty <- extract expr ctx
          unwrap <$> ensure' (_s::S_ "Const") ty error

        intro name ty ctx =
          Dhall.Core.shift 1 (AST.V name 0) <$>
            Dhall.Context.insert name (Dhall.Core.normalize (fst ty)) ctx

      in
      { "Const": unwrap >>> \c -> const $
          axiom c <#> AST.mkConst #
            V.liftW <<< V.noteSimple (_s::S_ "`Kind` has no type") unit
      , "Var": unwrap >>> \v@(AST.V name idx) ctx ->
          Dhall.Context.lookup name idx ctx #
            V.liftW <<< V.noteSimple (_s::S_ "Unbound variable") v
      , "Lam": \(AST.BindingBody name ty body) ctx -> do
          kA <- ensureConst_ctx ty ctx
            (V.liftW <<< V.errorSimple (_s::S_ "Invalid input type"))
          -- normalize (as part of `intro`) _after_ typechecking succeeds
          -- (in order to guarantee that normalization terminates)
          let ctx' = intro name ty ctx
          ty_body <- caramelize <$> extract body ctx'
          kB <- ensureConst_ctx ty_body ctx'
            (V.liftW <<< V.errorSimple (_s::S_ "Invalid output type"))
          _ <- rule kA kB #
            V.liftW <<< V.noteSimple (_s::S_ "No dependent types") (Tuple (fst ty) (fst ty_body))
          pure $ AST.mkPi name (fst ty) (fst ty_body)
      , "Pi": \(AST.BindingBody name ty ty_body) ctx -> do
          kA <- ensureConst_ctx ty ctx
            (V.liftW <<< V.errorSimple (_s::S_ "Invalid input type"))
          -- normalize (as part of `intro`) _after_ typechecking succeeds
          -- (in order to guarantee that normalization terminates)
          let ctx' = intro name ty ctx
          kB <- ensureConst_ctx ty_body ctx'
            (V.liftW <<< V.errorSimple (_s::S_ "Invalid output type"))

          map AST.mkConst $ rule kA kB #
            V.liftW <<< V.noteSimple (_s::S_ "No dependent types") (Tuple (fst ty) (fst ty_body))
      , "Let": \(AST.LetF name mty value expr) ctx -> do
          ty <- caramelize <$> extract value ctx
          for_ mty \ty' -> do
            _ <- extract ty' ctx
            if Dhall.Core.judgmentallyEqual (fst ty) (fst ty') then pure unit else
              V.liftW <<< V.errorSimple (_s::S_ "Annotation mismatch") $ unit
          kind <- extract ty ctx
          let
            name0 = AST.V name 0
            shiftIn = Dhall.Core.shift 1 name0
            shiftOut = Dhall.Core.shift (-1) name0
            subst = Dhall.Core.subst name0 $ shiftIn $ Dhall.Core.normalize $ fst value
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
              let ctx' = intro name ty ctx
              extract expr ctx' <#> subst >>> shiftOut
            handleType _ = fallback unit

            fallback _ =
              extract expr ctx <#> subst >>> shiftOut
          kind # Dhall.Core.normalize # AST.projectW #
            VariantF.on (_s::S_ "Const")
              (unwrap >>> handleType)
              \_ -> fallback unit
      }
    preservative =
      let
        onConst :: forall x.
          (x -> V.FeedbackR _ _ (Expr m s a)) ->
          Const.Const x (Onion _ _ m s a) ->
          CtxFb _ _ m s a
        onConst f (Const.Const c) _ = f c
        always :: forall x y. x -> y -> Context (Expr m s a) -> V.FeedbackR _ _ x
        always b _ _ = pure b
        aType :: forall x. Const.Const x (Onion _ _ m s a) -> CtxFb _ _ m s a
        aType = always $ AST.mkType
        aFunctor :: forall x. Const.Const x (Onion _ _ m s a) -> CtxFb _ _ m s a
        aFunctor = always $ AST.mkArrow AST.mkType AST.mkType
        a0 = AST.mkVar (AST.V "a" 0)

        -- TODO: This will need to become aware of AST holes
        -- Check a binary operation (`Pair` functor) against a simple, static,
        -- *normalized* type `t`.
        checkBinOp ::
          Expr m Void a ->
          Pair (Onion _ _ m s a) ->
          CtxFb _ _ m s a
        checkBinOp t p _ = suggest (lmap absurd t) $ for_ p $
          -- t should be simple enough that alphaNormalize is unnecessary
          \operand -> extract operand >>= Dhall.Core.normalize >>> case _ of
            ty_operand
              | t /= ty_operand -> V.liftW $ V.errorSimple
                (_s::S_ "Expected type") { expected: t, received: t }
              | otherwise -> pure unit

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
          Onion _ _ m s a ->
          (Unit -> V.FeedbackR _ _ Void) ->
          V.FeedbackR _ _ (f (Expr m s a))
        ensure s expr error = do
          ty <- extract expr
          ensure' s ty error

        -- Ensure that the passed `expr` is a term; i.e. the type of its type
        -- is `Type`. Returns the type of the `expr`.
        ensureTerm ::
          Onion _ _ m s a ->
          Context (Expr m s a) ->
          (Unit -> V.FeedbackR _ _ Void) ->
          V.FeedbackR _ _ (Expr m s a)
        ensureTerm expr ctx error = do
          ty <- extract expr
          ty <$ ensureType (caramelize ty <@> ctx) error

        -- Ensure that the passed `ty` is a type; i.e. its type is `Type`.
        ensureType ::
          Onion _ _ m s a ->
          (Unit -> V.FeedbackR _ _ Void) ->
          V.FeedbackR _ _ Unit
        ensureType ty error = do
          kind <- extract ty
          ensure' (_s::S_ "Const") kind error >>= case _ of
            Const.Const Type -> pure unit
            _ -> absurd <$> error unit


      in
      { "App": \(AST.Pair f a) c_t_x ->
          let
            checkFn = ensure (_s::S_ "Pi") f
              (V.liftW <<< V.errorSimple (_s::S_ "Not a function"))
            checkArg (AST.BindingBody name aty0 rty) aty1 =
              let name0 = AST.V name 0 in
              if Dhall.Core.judgmentallyEqual aty0 aty1
                then do
                  -- TODO: abstract this out
                  let a'    = Dhall.Core.shift   1  name0 (fst a)
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
                    V.liftW $ V.errorSimple (_s::S_ "Type mismatch")
                      { function: fst f
                      , expected: nf_aty0
                      , argument: fst a
                      , actual: nf_aty1
                      }
          in join $ checkArg <$> checkFn <*> extract a
      , "Annot": \(AST.Pair expr ty) c_t_x ->
          let
            checkEq aty0 aty1 =
              if Dhall.Core.judgmentallyEqual aty0 aty1 then pure aty0 else
                V.liftW <<< V.errorSimple (_s::S_ "Annotation mismatch") $ unit
          in join $ checkEq <$> extract expr <*> (fst ty <$ extract ty)
      , "Bool": identity aType
      , "BoolLit": always $ AST.mkBool
      , "BoolAnd": checkBinOp AST.mkBool
      , "BoolOr": checkBinOp AST.mkBool
      , "BoolEQ": checkBinOp AST.mkBool
      , "BoolNE": checkBinOp AST.mkBool
      , "BoolIf": \(AST.Triplet c t f) ctx ->
          ensure (_s::S_ "Bool") c
            (V.liftW <<< V.errorSimple (_s::S_ "Invalid predicate")) *>
          let
            checkMatch ty_t ty_f =
              if Dhall.Core.judgmentallyEqual ty_t ty_f then pure ty_t else
                V.liftW <<< V.errorSimple (_s::S_ "If branch mismatch") $ unit
          in join $ checkMatch
              <$> ensureTerm t ctx
                (V.liftW <<< V.errorSimple (_s::S_ "If branch must be term") <<< Tuple false)
              <*> ensureTerm f ctx
                (V.liftW <<< V.errorSimple (_s::S_ "If branch must be term") <<< Tuple true)
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
      , "ListLit": \(Product (Tuple mty lit)) ctx -> AST.mkApp AST.mkList <$> do
          -- get the assumed type of the list
          (ty :: Expr m s a) <- case mty of
            -- either from annotation
            Just ty -> suggest (fst ty) $
              ensureType ty
                (V.liftW <<< V.errorSimple (_s::S_ "Invalid list type"))
            -- or from the first element
            Nothing -> case Array.head lit of
              Nothing -> V.liftW <<< V.errorSimple (_s::S_ "Missing list type") $ unit
              Just item0 -> do
                ensureTerm item0 ctx
                  (V.liftW <<< V.errorSimple (_s::S_ "Invalid list type"))
          suggest ty $ forWithIndex_ lit \i item -> do
            ty' <- extract item
            if Dhall.Core.judgmentallyEqual ty ty' then pure unit else
              case mty of
                Nothing ->
                  V.liftW <<< V.errorSimple (_s::S_ "Invalid list element") $ i
                Just _ ->
                  V.liftW <<< V.errorSimple (_s::S_ "Mismatched list elements") $ i
      , "ListAppend": \p c_t_x -> AST.mkApp AST.mkList <$> do
          AST.Pair ty_l ty_r <- forWithIndex p \side expr -> do
            let error = V.liftW <<< V.errorSimple (_s::S_ "Cannot append non-list") <<< Tuple side
            expr_ty <- extract expr
            AST.Pair list ty <- ensure' (_s::S_ "App") expr_ty error
            Dhall.Core.normalize list # AST.projectW #
              VariantF.on (_s::S_ "List") (const (pure unit))
                \_ -> absurd <$> error unit
            pure ty
          if Dhall.Core.judgmentallyEqual ty_l ty_r then pure ty_l else
            V.liftW <<< V.errorSimple (_s::S_ "List append mistmatch") $ unit
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
      , "OptionalLit": \(Product (Tuple (Identity ty) mexpr)) c_t_x -> do
          ensureType ty
            (V.liftW <<< V.errorSimple (_s::S_ "Invalid optional type"))
          suggest (AST.mkApp AST.mkOptional (fst ty)) $
            for_ mexpr \expr -> do
              ty' <- extract expr
              if Dhall.Core.judgmentallyEqual (fst ty) ty' then pure unit else
                V.liftW <<< V.errorSimple (_s::S_ "Invalid optional element") $ unit
      , "Some": unwrap >>> \a ctx ->
          AST.mkApp AST.mkOptional <$> ensureTerm a ctx
            (V.liftW <<< V.errorSimple (_s::S_ "Invalid `Some`"))
      , "OptionalFold": always $ AST.mkForall "a" $
          AST.mkArrow (AST.mkApp AST.mkOptional a0) (optionalEnc a0)
      , "OptionalBuild": always $ AST.mkForall "a" $
          AST.mkArrow (optionalEnc a0) (AST.mkApp AST.mkOptional a0)
      , "Record": ?help
      , "RecordLit": ?help
      , "Union": \kts c_t_x ->
          -- FIXME: should this be the largest of `Type` or `Kind` returned?
          suggest AST.mkType $
            forWithIndex_ kts \field ty -> do
              void $ ensure (_s::S_ "Const") ty
                (V.liftW <<< V.errorSimple (_s::S_ "Invalid alternative type") <<< Tuple field)
      , "UnionLit": \(Product (Tuple (Tuple field (expr :: Onion _ _ m s a)) kts)) ctx -> do
          ty <- Dhall.Core.normalize <$> extract expr
          let kts' = StrMapIsh.insert field (caramelize ty <@> ctx) kts
          forWithIndex_ kts' \field ty -> do
            void $ ensure (_s::S_ "Const") ty
              (V.liftW <<< V.errorSimple (_s::S_ "Invalid alternative type") <<< Tuple field)
          pure $ AST.mkUnion $ fst <$> kts'
      , "Combine": ?help
      , "CombineTypes": ?help
      , "Prefer": ?help
      , "Merge": ?help
      , "Constructors": \(Identity ty) c_t_x -> do
          void $ extract ty
          kts <- fst ty # Dhall.Core.normalize # AST.projectW #
            VariantF.on (_s::S_ "Union") pure
              \_ -> V.liftW <<< V.errorSimple (_s::S_ "Constructors requires a union type") $ unit
          pure $ AST.mkRecord $ kts # mapWithIndex \field ty' ->
            AST.mkPi field ty' $ fst ty
      , "Field": \(Tuple field expr) ctx -> do
          ty <- extract expr
          let
            error _ = V.liftW <<< V.errorSimple (_s::S_ "Cannot access") $ field
            handleRecord kts = do
              -- FIXME
              -- _ <- loop ctx t
              case StrMapIsh.get field kts of
                Just ty -> pure ty
                Nothing -> V.liftW <<< V.errorSimple (_s::S_ "Missing field") $ field
            handleType kts = do
              case StrMapIsh.get field kts of
                Just ty -> pure $ AST.mkPi field ty $ fst expr
                Nothing -> V.liftW <<< V.errorSimple (_s::S_ "Missing field") $ field
            casing = (\_ -> error unit)
              # VariantF.on (_s::S_ "Record") handleRecord
              # VariantF.on (_s::S_ "Const") \(Const.Const c) ->
                  case c of
                    Type -> fst expr # Dhall.Core.normalize # AST.projectW #
                      VariantF.on (_s::S_ "Union") handleType (\_ -> error unit)
                    _ -> error unit
          ty # Dhall.Core.normalize # AST.projectW # casing
      , "Project": \(Tuple ks expr) ctx -> do
          kts <- ensure (_s::S_ "Record") expr
            (V.liftW <<< V.errorSimple (_s::S_ "Cannot project"))
          -- FIXME
          -- _ <- loop ctx t
          AST.mkRecord <$> forWithIndex ks \k (_ :: Unit) ->
            StrMapIsh.get k kts #
              (V.liftW <<< V.noteSimple (_s::S_ "Missing field") k)
      , "Note": \(Tuple s e) c_t_x ->
          V.scoped (_s::S_ "Note") s $
            extract e
      , "ImportAlt": \(Pair l _r) c_t_x ->
          -- FIXME???
          Dhall.Core.normalize <$> extract l
      , "Embed": onConst (pure <<< denote <<< tpa)
      }
  in VariantF.onMatch contextual \v ctx ->
      VariantF.match preservative (flip flap ctx <$> v) ctx

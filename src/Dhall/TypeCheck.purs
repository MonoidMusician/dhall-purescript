module Dhall.TypeCheck where

import Prelude

import Complex.Validation.These as V
import Control.Alternative (class Alternative)
import Control.Comonad (extract)
import Control.Plus (empty)
import Data.Array as Array
import Data.Bifunctor (lmap)
import Data.Const as Const
import Data.Either (Either(..))
import Data.Foldable (foldMap, for_)
import Data.FoldableWithIndex (forWithIndex_, traverseWithIndex_)
import Data.Functor.Product (Product(..))
import Data.Functor.Variant (FProxy(..), SProxy(..))
import Data.Functor.Variant as VariantF
import Data.FunctorWithIndex (class FunctorWithIndex, mapWithIndex)
import Data.Identity (Identity(..))
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap, wrap)
import Data.Profunctor.Strong (fanout)
import Data.Symbol (class IsSymbol)
import Data.Traversable (for)
import Data.TraversableWithIndex (forWithIndex)
import Data.Tuple (Tuple(..), fst)
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

type Fb ws es m s a = V.FeedbackR ws es (Expr m s a)
type CtxFb ws es m s a = Context (Expr m s a) -> Fb ws es m s a
type Onion ws es m s a = Tuple (Expr m s a) (CtxFb ws es m s a)

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

    carmelize :: Expr m s a -> Onion _ _ m s a
    carmelize = fanout identity $ flip $ typeWithA tpa

    ensureConst ::
      Onion _ _ m s a ->
      Context (Expr m s a) ->
      (Expr m s a -> V.FeedbackR _ _ Void) ->
      V.FeedbackR _ _ Const
    ensureConst expr ctx error =
      extract expr ctx
      >>= Dhall.Core.normalize >>> AST.projectW
      >>> VariantF.on (_s::S_ "Const") (pure <<< unwrap)
        \_ -> absurd <$> error (fst expr)

    ensure :: forall sym f r'.
      IsSymbol sym =>
      R.Cons sym (FProxy f) r' (AST.ExprLayerRow m s a) =>
      SProxy sym ->
      Onion _ _ m s a ->
      Context (Expr m s a) ->
      ({ expr :: Expr m s a, ty :: Expr m s a, nf_ty :: Expr m s a } -> V.FeedbackR _ _ Void) ->
      V.FeedbackR _ _ (f (Expr m s a))
    ensure s expr ctx error = do
      ty <- extract expr ctx
      ensure' s expr ty error

    ensure' :: forall sym f r'.
      IsSymbol sym =>
      R.Cons sym (FProxy f) r' (AST.ExprLayerRow m s a) =>
      SProxy sym ->
      Onion _ _ m s a ->
      Expr m s a ->
      ({ expr :: Expr m s a, ty :: Expr m s a, nf_ty :: Expr m s a } -> V.FeedbackR _ _ Void) ->
      V.FeedbackR _ _ (f (Expr m s a))
    ensure' s expr ty error =
      let nf_ty = Dhall.Core.normalize ty in
      AST.projectW nf_ty # VariantF.on s pure
        \_ -> absurd <$> error { expr: fst expr, ty, nf_ty }

    -- Ensure that the passed `expr` is a term; i.e. the type of its type
    -- is `Type`. Returns the type of the `expr`.
    ensureTerm ::
      Onion _ _ m s a ->
      Context (Expr m s a) ->
      ({ expr :: Expr m s a, ty :: Expr m s a, nf_ty :: Expr m s a } -> V.FeedbackR _ _ Void) ->
      V.FeedbackR _ _ (Expr m s a)
    ensureTerm expr ctx error = do
      ty <- extract expr ctx
      ty <$ ensureType (carmelize ty) ctx error

    -- Ensure that the passed `ty` is a type; i.e. its type is `Type`.
    ensureType ::
      Onion _ _ m s a ->
      Context (Expr m s a) ->
      ({ expr :: Expr m s a, ty :: Expr m s a, nf_ty :: Expr m s a } -> V.FeedbackR _ _ Void) ->
      V.FeedbackR _ _ Unit
    ensureType ty ctx error = do
      kind <- extract ty ctx
      ensure' (_s::S_ "Const") ty kind error >>= case _ of
        Const.Const Type -> pure unit
        _ -> absurd <$> error
          { expr: fst ty, ty: kind, nf_ty: Dhall.Core.normalize kind }

    check :: Expr m Void a -> Expr m Void a -> V.FeedbackR _ _ Unit
    check t t'
      | t /= t' = V.liftW $ V.errorSimple
        (_s::S_ "Expected type") { expected: t, received: t }
      | otherwise = pure unit

    checkBinOp ::
      Expr m Void a ->
      Pair (Onion _ _ m s a) ->
      CtxFb _ _ m s a
    checkBinOp t p ctx = suggest (lmap absurd t) $ for_ p
      \t' -> check t <<< Dhall.Core.normalize =<< extract t' ctx

    intro name ty ctx =
      Dhall.Core.shift 1 (AST.V name 0) <$>
        Dhall.Context.insert name (Dhall.Core.normalize (fst ty)) ctx

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

  in VariantF.match
    { "Const": onConst \c ->
        axiom c <#> AST.mkConst #
          V.liftW <<< V.noteSimple (_s::S_ "`Kind` has no type") unit
    , "Var": unwrap >>> \(AST.V name idx) ctx ->
        Dhall.Context.lookup name idx ctx #
          V.liftW <<< V.noteSimple (_s::S_ "Unbound variable") (AST.V name idx)
    , "Lam": \(AST.BindingBody name ty body) ctx -> do
        _ <- extract ty ctx
        -- normalize _after_ typechecking succeeds
        -- (so normalization is guaranteed to terminate)
        let ctx' = intro name ty ctx
        body_ty <- extract body ctx'
        let p = AST.mkPi name (fst ty) body_ty
        _ <- typeWithA tpa ctx p
        pure p
    , "Pi": \(AST.BindingBody name ty body) ctx -> do
        kA <- ensureConst ty ctx
          (V.liftW <<< V.errorSimple (_s::S_ "Invalid input type"))
        let ctx' = intro name ty ctx
        kB <- ensureConst body ctx'
          (V.liftW <<< V.errorSimple (_s::S_ "Invalid output type"))

        map AST.mkConst $ rule kA kB #
          V.liftW <<< V.noteSimple (_s::S_ "No dependent types") (Tuple (fst ty) (fst body))
    , "Let": \(AST.LetF name mty value expr) ctx -> do
        ty <- carmelize <$> extract value ctx
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
          handleType _ = handleTerm unit

          handleTerm _ =
            extract expr ctx <#> subst >>> shiftOut
        kind # Dhall.Core.normalize # AST.projectW #
          VariantF.on (_s::S_ "Const")
            (unwrap >>> handleType)
            \_ -> handleTerm unit
    , "App": \(AST.Pair f a) ctx ->
        -- TODO: recovery? if the variable is free in the resultant type?
        let
          checkFn = ensure (_s::S_ "Pi") f ctx
            (V.liftW <<< V.errorSimple (_s::S_ "Not a function"))
          checkArg (AST.BindingBody name aty0 rty) aty1 =
            if Dhall.Core.judgmentallyEqual aty0 aty1
              then do
                -- TODO: abstract this out
                let a'   = Dhall.Core.shift   1  (AST.V name 0) (fst a)
                let rty'  = Dhall.Core.subst (AST.V name 0) a' rty
                let rty'' = Dhall.Core.shift (-1) (AST.V name 0) rty'
                pure rty''
              else do
                let nf_aty0 = Dhall.Core.normalize aty0
                let nf_aty1 = Dhall.Core.normalize aty1
                V.liftW $ V.errorSimple (_s::S_ "Type mismatch")
                  { function: fst f
                  , expected: nf_aty0
                  , argument: fst a
                  , actual: nf_aty1
                  }
        in join $ checkArg <$> checkFn <*> extract a ctx
    , "Annot": \(AST.Pair expr ty) ctx ->
        let
          checkEq aty0 aty1 =
            if Dhall.Core.judgmentallyEqual aty0 aty1 then pure aty0 else
              V.liftW <<< V.errorSimple (_s::S_ "Annotation mismatch") $ unit
        in join $ checkEq <$> extract expr ctx <*> (fst ty <$ extract ty ctx)
    , "Bool": identity aType
    , "BoolLit": always $ AST.mkBool
    , "BoolAnd": checkBinOp AST.mkBool
    , "BoolOr": checkBinOp AST.mkBool
    , "BoolEQ": checkBinOp AST.mkBool
    , "BoolNE": checkBinOp AST.mkBool
    , "BoolIf": \(AST.Triplet c t f) ctx ->
        let
          ensureBool = void $ ensure (_s::S_ "Bool") c ctx
            (V.liftW <<< V.errorSimple (_s::S_ "Invalid predicate"))
          checkMatch ty_t ty_f =
            if Dhall.Core.judgmentallyEqual ty_t ty_f then pure ty_t else
              V.liftW <<< V.errorSimple (_s::S_ "If branch mismatch") $ unit
        in join $ const checkMatch <$> ensureBool
            <*> ensureTerm t ctx
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
        (ty :: Expr m s a) <- case mty of
          Just ty -> suggest (fst ty) $
            ensureType ty ctx
              (V.liftW <<< V.errorSimple (_s::S_ "Invalid list type"))
          Nothing -> case Array.head lit of
            Nothing -> V.liftW <<< V.errorSimple (_s::S_ "Missing list type") $ unit
            Just item0 -> do
              ensureTerm item0 ctx
                (V.liftW <<< V.errorSimple (_s::S_ "Invalid list type"))
        suggest (ty) $ forWithIndex_ lit \i item -> do
          ty' <- extract item ctx
          if Dhall.Core.judgmentallyEqual ty ty' then pure unit else
            case mty of
              Nothing ->
                V.liftW <<< V.errorSimple (_s::S_ "Invalid list element") $ i
              Just _ ->
                V.liftW <<< V.errorSimple (_s::S_ "Mismatched list elements") $ i
    , "ListAppend": \p ctx -> AST.mkApp AST.mkList <$> do
        AST.Pair ty_l ty_r <- forWithIndex p \side expr -> do
          let error = V.liftW <<< V.errorSimple (_s::S_ "Cannot append non-list") <<< Tuple side
          expr_ty <- extract expr ctx
          AST.Pair list ty <- ensure' (_s::S_ "App") expr expr_ty error
          Dhall.Core.normalize list # AST.projectW #
            VariantF.on (_s::S_ "List") (const (pure unit))
              \_ -> absurd <$> error
                { expr: fst expr, ty: expr_ty, nf_ty: Dhall.Core.normalize expr_ty }
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
    , "OptionalLit": \(Product (Tuple (Identity ty) mexpr)) ctx -> do
        ensureType ty ctx
          (V.liftW <<< V.errorSimple (_s::S_ "Invalid optional type"))
        suggest (AST.mkApp AST.mkOptional (fst ty)) $
          for_ mexpr \expr -> do
            ty' <- extract expr ctx
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
    , "Union": \kts ctx ->
        -- FIXME: should this be the largest of `Type` or `Kind` returned?
        suggest AST.mkType $
          forWithIndex_ kts \field ty -> do
            void $ ensureConst ty ctx
              (V.liftW <<< V.errorSimple (_s::S_ "Invalid alternative type") <<< Tuple field)
    , "UnionLit": \(Product (Tuple (Tuple field expr) kts)) ctx -> do
        ty <- Dhall.Core.normalize <$> extract expr ctx
        let union = AST.mkUnion $ StrMapIsh.insert field ty (fst <$> kts)
        union <$ typeWithA tpa ctx union
    , "Combine": ?help
    , "CombineTypes": ?help
    , "Prefer": ?help
    , "Merge": ?help
    , "Constructors": \(Identity ty) ctx -> do
        void $ extract ty ctx
        kts <- fst ty # Dhall.Core.normalize # AST.projectW #
          VariantF.on (_s::S_ "Union") pure
            \_ -> V.liftW <<< V.errorSimple (_s::S_ "Constructors requires a union type") $ unit
        pure $ AST.mkRecord $ kts # mapWithIndex \field ty' ->
          AST.mkPi field ty' $ fst ty
    , "Field": \(Tuple field expr) ctx -> do
        ty <- extract expr ctx
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
        kts <- ensure (_s::S_ "Record") expr ctx
          (V.liftW <<< V.errorSimple (_s::S_ "Cannot project"))
        -- FIXME
        -- _ <- loop ctx t
        AST.mkRecord <$> forWithIndex ks \k (_ :: Unit) ->
          StrMapIsh.get k kts #
            (V.liftW <<< V.noteSimple (_s::S_ "Missing field") k)
    , "Note": \(Tuple s e) ctx ->
        V.scoped (_s::S_ "Note") s $
          extract e ctx
    , "ImportAlt": \(Pair l _r) ctx ->
        -- FIXME???
        Dhall.Core.normalize <$> extract l ctx
    , "Embed": onConst (pure <<< denote <<< tpa)
    }

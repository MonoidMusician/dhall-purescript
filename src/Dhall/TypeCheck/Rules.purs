module Dhall.TypeCheck.Rules where

import Prelude

import Control.Alternative (class Alternative, (<|>))
import Control.Apply (lift2)
import Control.Comonad (extract)
import Control.Comonad.Env (EnvT(..))
import Control.Plus (empty)
import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Const as Const
import Data.Either (Either(..))
import Data.Foldable (class Foldable, foldMap, foldlDefault, foldrDefault, traverse_)
import Data.FoldableWithIndex (class FoldableWithIndex, foldMapWithIndex, forWithIndex_)
import Data.Functor.App (App(..))
import Data.Functor.Compose (Compose(..))
import Data.Functor.Product (Product(..))
import Data.Functor.Variant (FProxy, SProxy)
import Data.Functor.Variant as VariantF
import Data.FunctorWithIndex (class FunctorWithIndex, mapWithIndex)
import Data.Identity (Identity(..))
import Data.Lens.Record (prop)
import Data.List (List(..), (:))
import Data.List as List
import Data.List.NonEmpty (foldMap1)
import Data.List.NonEmpty as NEL
import Data.List.Types (NonEmptyList(..))
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Maybe.First (First(..))
import Data.Newtype (un, unwrap, wrap)
import Data.NonEmpty ((:|))
import Data.Ord.Max (Max(..))
import Data.Set as Set
import Data.Symbol (class IsSymbol)
import Data.These (These(..))
import Data.Traversable (for, traverse)
import Data.TraversableWithIndex (forWithIndex, traverseWithIndex)
import Data.Tuple (Tuple(..), curry, fst, uncurry)
import Data.Variant as Variant
import Dhall.Context as Dhall.Context
import Dhall.Core (SimpleExpr, rehydrate)
import Dhall.Core.AST (Const(..), Expr, Pair(..), S_, _S)
import Dhall.Core.AST as AST
import Dhall.Map (class MapLike)
import Dhall.Map as Dhall.Map
import Dhall.TypeCheck.Operations (alsoOriginateFromO, areEq, newborn, newshared, normalizeStep, plain, topLoc, tryShiftOut0Oxpr, typecheckStep, unlayerO)
import Dhall.TypeCheck.Tree (shared, unshared)
import Dhall.TypeCheck.Types (Errors, FeedbackE, Inconsistency(..), L, LxprF, OsprE, Oxpr, OxprE, TypeCheckError(..), WithBiCtx(..))
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

-- Compute groupings according to an equivalence relation
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

-- A helper for consistency checks: add an extra "hint" or first element to an
-- existing foldable container.
data WithHint f a = WithHint (Maybe a) (f a)
derive instance functorWithHint :: Functor f => Functor (WithHint f)
instance functorWithIndexWithHint :: FunctorWithIndex i f => FunctorWithIndex (Maybe i) (WithHint f) where
  mapWithIndex f (WithHint ma fa) = WithHint (f Nothing <$> ma) (mapWithIndex (f <<< Just) fa)
instance foldableWithHint :: Foldable f => Foldable (WithHint f) where
  foldMap f (WithHint ma fa) = foldMap f ma <> foldMap f fa
  foldl f = foldlDefault f
  foldr f = foldrDefault f

-- Ensure that a list of Oxprs match up, returning a common representative if so
-- (with locations conglomerated).
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

typecheckAlgebra :: forall w r m a. Eq a => MapLike String m =>
  (a -> FeedbackE w r m a (Expr m a)) ->
  WithBiCtx (LxprF m a) (OxprE w r m a) -> FeedbackE w r m a (OsprE w r m a)
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

    newb = unshared <<< newborn
    mkFunctor :: Expr m a -> OsprE w r m a -> OsprE w r m a
    mkFunctor f a = mkShared (_S::S_ "App") $
      Pair (newb f) a
    mkShared :: forall sym f r'.
      Functor f =>
      IsSymbol sym =>
      R.Cons sym (FProxy f) r' (AST.ExprLayerRow m a) =>
      SProxy sym ->
      f (OsprE w r m a) ->
      OsprE w r m a
    mkShared sym = newshared <<< VariantF.inj sym
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
    checkEqL ty0 ty1 error = V.confirmW ty0 $ checkEq ty0 ty1 error
    checkEqR ::
      OxprE w r m a -> OxprE w r m a ->
      (Unit -> FeedbackE w r m a Void) ->
      FeedbackE w r m a (OxprE w r m a)
    checkEqR ty0 ty1 error = V.confirmW ty1 $ checkEq ty0 ty1 error

    always :: forall y. Expr m a -> y -> FeedbackE w r m a (OsprE w r m a)
    always b _ = pure $ newb $ b
    aType :: forall x. Const.Const x (OxprE w r m a) -> FeedbackE w r m a (OsprE w r m a)
    aType = always $ AST.mkType
    aFunctor :: forall x. Const.Const x (OxprE w r m a) -> FeedbackE w r m a (OsprE w r m a)
    aFunctor = always $ AST.mkArrow AST.mkType AST.mkType
    a0 = AST.mkVar (AST.V "a" 0)

    -- TODO: This will need to become aware of AST holes
    -- Check a binary operation (`Pair` functor) against a simple, static,
    -- *normalize* type `t`.
    checkBinOp ::
      SimpleExpr ->
      Pair (OxprE w r m a) ->
      FeedbackE w r m a (OsprE w r m a)
    checkBinOp t p = V.confirmW (newb (rehydrate t)) $ forWithIndex_ p $
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

    ensureAnyTerm ::
      OxprE w r m a ->
      (Unit -> FeedbackE w r m a Void) ->
      FeedbackE w r m a (OxprE w r m a)
    ensureAnyTerm expr error = do
      ty <- typecheckStep expr
      kind <- typecheckStep ty
      ty <$ ensure' (_S::S_ "Const") kind error

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
      axiom c <#> newb <<< AST.mkConst #
        noteHere (_S::S_ "`Sort` has no type") unit
  , "Var": unwrap >>> \v@(AST.V name idx) ->
      case Dhall.Context.lookup name idx ctx of
        -- NOTE: this should always succeed, since the body is checked only
        -- after the `Let` value succeeds.
        Just (This value) -> shared <$> typecheckStep value
        Just (That ty) -> pure $ shared ty
        Just (Both _ ty) -> pure $ shared ty
        Nothing ->
          errorHere (_S::S_ "Unbound variable") v
  , "Lam": \(AST.BindingBody name ty body) -> do
      kI <- ensureConst ty
        (errorHere (_S::S_ "Invalid input type"))
      ty_body <- typecheckStep body
      kO <- ensureConst ty_body
        (errorHere (_S::S_ "Invalid output type"))
      pure $ mkShared(_S::S_"Pi") (AST.BindingBody name (shared ty) (shared ty_body))
  , "Pi": \(AST.BindingBody name ty ty_body) -> do
      kI <- ensureConst ty
        (errorHere (_S::S_ "Invalid input type"))
      kO <- ensureConst ty_body
        (errorHere (_S::S_ "Invalid output type"))
      map (newb <<< AST.mkConst) $ rule kI kO
  , "Let": \(AST.LetF name mty value expr) -> do
      ty0 <- typecheckStep value
      ty <- fromMaybe ty0 <$> for mty \ty' -> do
        _ <- typecheckStep ty'
        checkEqR ty0 ty'
          (errorHere (_S::S_ "Annotation mismatch"))
      ty_expr <- typecheckStep expr
      let shifted = tryShiftOut0Oxpr name ty_expr
      pure case shifted of
        Nothing -> mkShared(_S::S_"Let") (shared <$> AST.LetF name mty value ty_expr)
        Just ty_expr' -> shared ty_expr'
  , "App": \(AST.Pair f a) ->
      let
        checkFn = ensure (_S::S_ "Pi") f
          (errorHere (_S::S_ "Not a function"))
        checkArg (AST.BindingBody name aty0 rty) aty1 =
          let shifted = tryShiftOut0Oxpr name rty in
          if areEq aty0 aty1
            then pure case shifted of
              Nothing -> mkShared(_S::S_"App") $ Pair
                do mkShared(_S::S_"Lam") (shared <$> AST.BindingBody name aty0 rty)
                do shared a
              Just rty' -> shared rty'
            else do
              -- SPECIAL!
              -- Recovery case: if the variable is unused in the return type
              -- then this is a non-dependent function
              -- and its return type can be suggested
              -- even if its argument does not have the right type
              errorHere (_S::S_ "Type mismatch") unit # case shifted of
                Nothing -> identity
                Just rty' -> V.confirmW (shared rty')
      in join $ checkArg <$> checkFn <*> typecheckStep a
  , "Annot": \(AST.Pair expr ty) ->
      map shared $ join $ checkEqR
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
      pure $ newb AST.mkType
  , "Assert": \(Identity equiv) -> do
      Pair l r <- ensure' (_S::S_ "Equivalent") equiv
        (errorHere (_S::S_ "Not an equivalence"))
      _ <- checkEqR l r
        (errorHere (_S::S_ "Assertion failed"))
      pure $ shared equiv
  , "Bool": identity aType
  , "BoolLit": always $ AST.mkBool
  , "BoolAnd": checkBinOp AST.mkBool
  , "BoolOr": checkBinOp AST.mkBool
  , "BoolEQ": checkBinOp AST.mkBool
  , "BoolNE": checkBinOp AST.mkBool
  , "BoolIf": \(AST.Triplet c t f) ->
      ensure (_S::S_ "Bool") c
        (errorHere (_S::S_ "Invalid predicate")) *> do
      map shared $ join $ checkEqL
          <$> ensureAnyTerm t
            (errorHere (_S::S_ "If branch must be term") <<< const false)
          <*> ensureAnyTerm f
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
  , "NaturalSubtract": always $ AST.mkArrow AST.mkNatural $ AST.mkArrow AST.mkNatural AST.mkNatural
  , "NaturalPlus": checkBinOp AST.mkNatural
  , "NaturalTimes": checkBinOp AST.mkNatural
  , "Integer": identity aType
  , "IntegerLit": always $ AST.mkInteger
  , "IntegerShow": always $ AST.mkArrow AST.mkInteger AST.mkText
  , "IntegerToDouble": always $ AST.mkArrow AST.mkInteger AST.mkDouble
  , "IntegerNegate": always $ AST.mkArrow AST.mkInteger AST.mkInteger
  , "IntegerClamp": always $ AST.mkArrow AST.mkInteger AST.mkNatural
  , "Double": identity aType
  , "DoubleLit": always $ AST.mkDouble
  , "DoubleShow": always $ AST.mkArrow AST.mkDouble AST.mkText
  , "Text": identity aType
  , "TextLit": \things -> V.confirmW (newb AST.mkText) $
      forWithIndex_ things \i expr -> ensure (_S::S_ "Text") expr
        (errorHere (_S::S_ "Cannot interpolate") <<< const i)
  , "TextAppend": checkBinOp AST.mkText
  , "TextShow": always $ AST.mkArrow AST.mkText AST.mkText
  , "TextReplace": always $
      AST.mkPi "needle" AST.mkText $
        AST.mkPi "replacement" AST.mkText $
          AST.mkPi "haystack" AST.mkText $
            AST.mkText
  , "List": identity aFunctor
  , "ListLit": \(Product (Tuple mty lit)) -> V.mconfirmW (shared <$> mty) do
      -- get the assumed type of the list
      (ty :: OxprE w r m a) <- case mty of
        -- either from annotation
        Just listty -> do
          let error = errorHere (_S::S_ "List annotation must be list type")
          AST.Pair list ty <- ensure' (_S::S_ "App") listty error
          normalizeStep list # unlayerO #
            VariantF.on (_S::S_ "List") (const (pure unit))
              \_ -> absurd <$> error unit
          V.confirmW ty $ ensureType ty
            (errorHere (_S::S_ "Invalid list type"))
        -- or from the first element
        Nothing -> case Array.head lit of
          Nothing -> errorHere (_S::S_ "Missing list type") $ unit
          Just item -> do
            ensureTerm item
              (errorHere (_S::S_ "Invalid list type"))
      V.confirmW (mkFunctor AST.mkList (shared ty)) $ forWithIndex_ lit \i item -> do
        ty' <- typecheckStep item
        checkEq ty ty' \_ ->
          case mty of
            Nothing ->
              errorHere (_S::S_ "Invalid list element") $ i
            Just _ ->
              errorHere (_S::S_ "Mismatched list elements") $ i
  , "ListAppend": \p -> mkFunctor AST.mkList <<< shared <$> do
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
      mkFunctor AST.mkOptional <<< shared <$> ensureTerm a
        (errorHere (_S::S_ "Invalid `Some`"))
  , "Record": \kts ->
      ensureNodupes
        (errorHere (_S::S_ "Duplicate record fields")) kts
      *> do
        kts' <- forWithIndex kts \field ty -> do
          unwrap <$> ensure (_S::S_ "Const") ty
            (errorHere (_S::S_ "Invalid field type") <<< const field)
        pure $ newb $ AST.mkConst $ maxConst kts'
  , "RecordLit": \kvs ->
      ensureNodupes
        (errorHere (_S::S_ "Duplicate record fields")) kvs
      *> do
        kts <- traverse typecheckStep kvs
        V.confirmW (mkShared(_S::S_"Record") (shared <$> kts)) do
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
        pure $ newb $ AST.mkConst $ maxConst kts'
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
          mkShared(_S::S_"Record") <$> forWithIndex combined \k ->
            case _ of
              Both ktsL' ktsR' ->
                combineTypes (k : here) (AST.Pair ktsL' ktsR')
              This t -> pure (shared t)
              That t -> pure (shared t)
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
              This t -> pure (shared t)
              That t -> pure (shared t)
          pure { const: max constL constR, rec: mkShared(_S::S_"Record") kts }
      in map (newb <<< AST.mkConst <<< _.const) <<< combineTypes Nil
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
      pure $ mkShared(_S::S_"Record") $ map shared $ Dhall.Map.unionWith (pure preference) ktsR ktsL
  , "RecordCompletion": \(AST.Pair l r) -> do
      AST.Pair lT rT <- traverse typecheckStep (AST.Pair l r)
      fields <- ensure' (_S::S_ "RecordLit") l
        (errorHere (_S::S_ "Cannot access"))
      AST.Pair df dest <- AST.Pair
        <$> (Dhall.Map.get "default" fields # noteHere (_S::S_ "Missing field") "default")
        <*> (Dhall.Map.get "Type" fields # noteHere (_S::S_ "Missing field") "Type")
      fields' <- ensure' (_S::S_ "Record") dest
        (errorHere (_S::S_ "Annotation mismatch"))
      V.confirmW (shared dest) do
        let p = AST.Pair df r
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
          comparing = case _ of
            Both l' r' -> checkEqR l' r' (errorHere (_S::S_ "Annotation mismatch"))
            _ -> errorHere (_S::S_ "Annotation mismatch") unit
          res = Dhall.Map.unionWith (pure preference) ktsR ktsL
        void $ traverse identity $ Dhall.Map.unionWith (pure (Just <<< comparing)) res fields'
  , "With": \(Product (Tuple (Identity e) (Tuple ks0 v))) -> do
      AST.Pair eT vT <- traverse typecheckStep (AST.Pair e v)
      let
        addfield ks t = do
          kts <- ensure' (_S::S_ "Record") t
            (errorHere (_S::S_ "Must combine a record") <<< const (Tuple Nil false))
          mkShared (_S::S_ "Record") <$> case NEA.fromArray (NEA.tail ks) of
            Nothing -> pure $ map shared $ Dhall.Map.insert (NEA.head ks) vT kts
            Just ks' -> do
              changed <- forWithIndex kts \k' t' ->
                if k' /= NEA.head ks then pure (shared t') else addfield ks' t'
              pure $ changed # Dhall.Map.alter (NEA.head ks)
                case _ of
                  Nothing -> Just $
                    Array.foldr (\k v' -> mkShared (_S::S_ "Record") (Dhall.Map.singleton k v')) (shared vT) ks'
                  Just yes -> Just yes
      addfield ks0 eT
  , "Merge": \(AST.MergeF handlers cases mty) -> do
      Tuple ktsX (Compose ktsY) <- Tuple
        <$> ensure (_S::S_ "Record") handlers
          (errorHere (_S::S_ "Must merge a record"))
        <*> do
          tyY <- typecheckStep cases
          let
            error = errorHere (_S::S_ "Must merge a union")
            casing = (\_ -> absurd <$> error unit)
              # VariantF.on (_S::S_ "Union") pure
              # VariantF.on (_S::S_ "App") \(AST.Pair f t) -> do
                  void $ ensure' (_S::S_ "Optional") f error
                  pure $ Compose $ Dhall.Map.fromFoldable
                    [ Tuple "Some" (Just t)
                    , Tuple "None" Nothing
                    ]
          tyY # normalizeStep # unlayerO # casing
      let
        ksX = Set.fromFoldable $ ((fst <$> Dhall.Map.toUnfoldable ktsX) :: List String)
        ksY = Set.fromFoldable $ ((fst <$> Dhall.Map.toUnfoldable ktsY) :: List String)
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
      V.confirmW (shared ty) ado
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
  , "ToMap": \(Product (Tuple (Identity expr) mty)) -> V.mconfirmW (shared <$> mty) do
      kts <- ensure (_S::S_ "Record") expr
        (errorHere (_S::S_ "toMap takes a record"))
      let
        mapType ty =
          mkFunctor AST.mkList $ mkShared(_S::S_ "Record") $ Dhall.Map.fromFoldable
            [ Tuple "mapKey" $ mkShared(_S::S_ "Text") (wrap unit)
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
        V.confirmW ty $ ensureType ty (errorHere (_S::S_ "Invalid toMap type"))
      ty <- ensureConsistentOxpr
        (errorHere (_S::S_ "Missing toMap type"))
        (errorHere (_S::S_ "Inconsistent toMap types") <<< (map <<< map) _.key)
        (WithHint tyA kts)
      void $ ensureType ty (errorHere (_S::S_ "Invalid toMap type annotation") <<< const unit)
      pure $ mapType $ shared ty
  , "Field": \(Tuple field expr) -> do
      tyR <- typecheckStep expr
      let
        error _ = errorHere (_S::S_ "Cannot access") unit
        handleRecord kts = do
          case Dhall.Map.get field kts of
            Just ty -> pure (shared ty)
            Nothing -> errorHere (_S::S_ "Missing field") $ field
        handleType kts = do
          case Dhall.Map.get field kts of
            Just (Just ty) -> pure $ mkShared(_S::S_"Pi") $ map shared $ (AST.BindingBody field ty expr)
            Just Nothing -> pure $ shared expr
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
      mkShared(_S::S_"Record") <<< map shared <$> forWithIndex ks \k mty -> do
        ty0 <- Dhall.Map.get k kts #
          (noteHere (_S::S_ "Missing field") k)
        mty # maybe (pure ty0) \ty1 ->
          checkEqR ty0 ty1 (errorHere (_S::S_ "Projection type mismatch") <<< const k)
  , "Hashed": \(Tuple _ e) -> shared <$> typecheckStep e
  , "UsingHeaders": \(Pair l r) ->
      shared <$> typecheckStep l <* do
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
      case unwrap $ shared <$> typecheckStep l of
        succ@(V.Success _) -> wrap succ
        V.Error es ml ->
          case unwrap $ shared <$> typecheckStep r of
            succ@(V.Success _) -> wrap succ
            V.Error es' mr -> wrap $ V.Error (es <> es') (ml <|> mr)
  , "Embed": map newb <<< tpa <<< unwrap
  }

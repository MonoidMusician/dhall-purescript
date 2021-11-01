module Dhall.TypeCheck.MoreOperations where


import Prelude

import Data.Const as Const
import Data.FoldableWithIndex (forWithIndex_)
import Data.Functor.Variant as VariantF
import Data.Map (SemigroupMap(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Ord.Max (Max(..))
import Data.Symbol (class IsSymbol)
import Data.Tuple (Tuple(..))
import Data.Variant as Variant
import Dhall.Core (SimpleExpr, rehydrate)
import Dhall.Core.AST (Const(..), Expr, Pair(..), S_, _S)
import Dhall.Core.AST as AST
import Dhall.Lib.MonoidalState (LocStateErroring(..))
import Dhall.Lib.MonoidalState as V
import Dhall.Map (class MapLike)
import Dhall.TypeCheck.Operations (newborn, newshared, normalizeStep, plain, typecheckStep, unify, unlayerO)
import Dhall.TypeCheck.Tree (unshared)
import Dhall.TypeCheck.Types (Errors, LFeedbackE, OsprE, OxprE)
import Type.Proxy (Proxy)
import Type.Row as R


errorHere ::
  forall sym t r' b w r m a. Eq a => MapLike String m =>
    IsSymbol sym =>
    R.Cons sym t r' (Errors r) =>
  Proxy sym ->
  t ->
  LFeedbackE w r m a b
errorHere sym v =
  LocStateErroring \loc -> V.erroring $ Tuple loc $ Variant.inj sym v

noteHere ::
  forall sym t r' b w r m a. Eq a => MapLike String m =>
    IsSymbol sym =>
    R.Cons sym t r' (Errors r) =>
  Proxy sym ->
  t ->
  Maybe b ->
  LFeedbackE w r m a b
noteHere sym v Nothing = errorHere sym v
noteHere _ _ (Just b) = pure b

tyStep :: forall w r m a. Eq a => MapLike String m => OxprE w r m a -> LFeedbackE w r m a (OxprE w r m a)
tyStep = V.liftR <<< typecheckStep

uniError :: forall w r m a b. Eq a => MapLike String m => Pair Const -> LFeedbackE w r m a b
uniError = errorHere (_S::S_ "Universes could not unify")

newb :: forall w r m a. Eq a => MapLike String m => Expr m a -> OsprE w r m a
newb = unshared <<< newborn

mkFunctor :: forall w r m a. Eq a => MapLike String m => Expr m a -> OsprE w r m a -> OsprE w r m a
mkFunctor f a = mkShared (_S::S_ "App") $
  Pair (newb f) a
mkShared :: forall sym f r' w r m a. Eq a => MapLike String m =>
  Functor f =>
  IsSymbol sym =>
  R.Cons sym f r' (AST.ExprLayerRow m a) =>
  Proxy sym ->
  f (OsprE w r m a) ->
  OsprE w r m a
mkShared sym = newshared <<< VariantF.inj sym
ensure' :: forall sym f r' w r m a. Eq a => MapLike String m =>
  IsSymbol sym =>
  R.Cons sym f r' (AST.ExprLayerRow m a) =>
  Proxy sym ->
  OxprE w r m a ->
  (Unit -> LFeedbackE w r m a Void) ->
  LFeedbackE w r m a (f (OxprE w r m a))
ensure' s ty error =
  let nf_ty = normalizeStep ty in
  unlayerO nf_ty # VariantF.on s pure
    \_ -> absurd <$> error unit
ensureConst :: forall w r m a. Eq a => MapLike String m =>
  OxprE w r m a ->
  (Unit -> LFeedbackE w r m a Void) ->
  LFeedbackE w r m a Const
ensureConst expr error = do
  ty <- V.escalateR (tyStep expr)
  unwrap <$> ensure' (_S::S_ "Const") ty error

checkEq :: forall w r m a. Eq a => MapLike String m =>
  OxprE w r m a -> OxprE w r m a ->
  (Unit -> LFeedbackE w r m a Void) ->
  LFeedbackE w r m a Unit
checkEq ty0 ty1 error =
  unify error uniError ty0 ty1
checkEqL :: forall w r m a. Eq a => MapLike String m =>
  OxprE w r m a -> OxprE w r m a ->
  (Unit -> LFeedbackE w r m a Void) ->
  LFeedbackE w r m a (OxprE w r m a)
checkEqL ty0 ty1 error = V.confirmR ty0 $ checkEq ty0 ty1 error
checkEqR :: forall w r m a. Eq a => MapLike String m =>
  OxprE w r m a -> OxprE w r m a ->
  (Unit -> LFeedbackE w r m a Void) ->
  LFeedbackE w r m a (OxprE w r m a)
checkEqR ty0 ty1 error = V.confirmR ty1 $ checkEq ty0 ty1 error

always :: forall y w r m a. Eq a => MapLike String m => Expr m a -> y -> LFeedbackE w r m a (OsprE w r m a)
always b _ = pure $ newb $ b
aType :: forall x w r m a. Eq a => MapLike String m => Const.Const x (OxprE w r m a) -> LFeedbackE w r m a (OsprE w r m a)
aType = always $ AST.mkType zero
aFunctor :: forall x w r m a. Eq a => MapLike String m => Const.Const x (OxprE w r m a) -> LFeedbackE w r m a (OsprE w r m a)
aFunctor = always $ AST.mkArrow (AST.mkType zero) (AST.mkType zero)

-- TODO: This will need to become aware of AST holes
-- Check a binary operation (`Pair` functor) against a simple, static,
-- *normalize* type `t`.
checkBinOp :: forall w r m a. Eq a => MapLike String m =>
  SimpleExpr ->
  Pair (OxprE w r m a) ->
  LFeedbackE w r m a (OsprE w r m a)
checkBinOp t p = V.confirmR (newb (rehydrate t)) $ forWithIndex_ p $
  -- t should be simple enough that alphaNormalize is unnecessary
  \side operand -> V.escalateR (tyStep operand) >>= normalizeStep >>> case _ of
    ty_operand | rehydrate t == plain ty_operand -> pure unit
      | otherwise -> errorHere
        (_S::S_ "Unexpected type") (Tuple side t)

ensure :: forall sym f r' w r m a. Eq a => MapLike String m =>
  IsSymbol sym =>
  R.Cons sym f r' (AST.ExprLayerRow m a) =>
  Proxy sym ->
  OxprE w r m a ->
  (Unit -> LFeedbackE w r m a Void) ->
  LFeedbackE w r m a (f (OxprE w r m a))
ensure s expr error = do
  ty <- V.escalateR (tyStep expr)
  ensure' s ty error

-- Ensure that the passed `expr` is a term; i.e. the type of its type
-- is `Type`. Returns the type of the `expr`.
ensureTerm :: forall w r m a. Eq a => MapLike String m =>
  OxprE w r m a ->
  (Maybe Const -> LFeedbackE w r m a Void) ->
  LFeedbackE w r m a (OxprE w r m a)
ensureTerm expr error = do
  ty <- V.escalateR (tyStep expr)
  ty <$ ensureType ty error

ensureAnyTerm :: forall w r m a. Eq a => MapLike String m =>
  OxprE w r m a ->
  (Unit -> LFeedbackE w r m a Void) ->
  LFeedbackE w r m a (OxprE w r m a)
ensureAnyTerm expr error = do
  ty <- V.escalateR (tyStep expr)
  kind <- tyStep ty
  ty <$ ensure' (_S::S_ "Const") kind error

-- Ensure that the passed `ty` is a type; i.e. its type is `Type`.
ensureType :: forall w r m a. Eq a => MapLike String m =>
  OxprE w r m a ->
  (Maybe Const -> LFeedbackE w r m a Void) ->
  LFeedbackE w r m a Unit
ensureType ty error = do
  kind <- V.escalateR (tyStep ty)
  ensure' (_S::S_ "Const") kind (\_ -> error Nothing) >>= case _ of
    -- TODO
    Const.Const (Universes (SemigroupMap m) (Max 0)) | Map.isEmpty m -> pure unit
    Const.Const c -> absurd <$> error (Just c)

module Dhall.Normalize.Apps where

import Prelude

import Data.Const (Const)
import Data.Functor.Variant (VariantF)
import Data.Lens as Lens
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Maybe (Maybe(..))
import Dhall.Core.AST (Expr, S_, _S)
import Dhall.Core.AST as AST

-- Little ADT to make destructuring applications easier for normalization
data Apps m a = App (Apps m a) (Apps m a) | NoApp (Expr m a)
infixl 0 App as ~

noapplit :: forall m a v.
  Lens.Prism'
    (VariantF (AST.ExprLayerRow m a) (Expr m a))
    (Const v (Expr m a)) ->
  Apps m a ->
  Maybe v
noapplit p = Lens.preview (_NoApp <<< AST._E p <<< _Newtype)

noapplit' :: forall f m a. Functor f =>
  Lens.Prism'
    (VariantF (AST.ExprLayerRow m a) (Expr m a))
    (f (Expr m a)) ->
  Apps m a ->
  Maybe (f (Expr m a))
noapplit' p = Lens.preview (_NoApp <<< AST._E p)

noapp :: forall f m a. Functor f =>
  Lens.Prism'
    (VariantF (AST.ExprLayerRow m a) (Expr m a))
    (f (Expr m a)) ->
  Apps m a ->
  Boolean
noapp p = Lens.is (_NoApp <<< AST._E p)

_NoApp :: forall m a. Lens.Prism' (Apps m a) (Expr m a)
_NoApp = Lens.prism' NoApp case _ of
  NoApp e -> Just e
  _ -> Nothing

apps :: forall m a. Lens.Iso' (Expr m a) (Apps m a)
apps = Lens.iso fromExpr toExpr where
  toExpr = case _ of
    App f a -> AST.mkApp (toExpr f) (toExpr a)
    NoApp e -> e
  fromExpr e =
    case Lens.preview (AST._E (AST._ExprFPrism (_S::S_ "App"))) e of
      Nothing -> NoApp e
      Just (AST.Pair fn arg) -> App (fromExpr fn) (fromExpr arg)

module Dhall.Normalize.Apps where

import Prelude

import Data.Const (Const)
import Data.Functor.Variant (VariantF)
import Data.Functor.Variant as VariantF
import Data.Lens as Lens
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Maybe (Maybe(..), isJust)
import Data.Newtype (unwrap)
import Data.Symbol (class IsSymbol)
import Dhall.Core.AST (Expr, S_, _S)
import Dhall.Core.AST as AST
import Prim.Row as Row
import Type.Proxy (Proxy)

-- Little ADT to make destructuring applications easier for normalization
data AppsF a = App (AppsF a) (AppsF a) | NoApp a
infixl 0 App as ~
derive instance functorApps :: Functor AppsF
instance applyApps :: Apply AppsF where
  apply = ap
instance applicativeApps :: Applicative AppsF where
  pure = NoApp
instance bindApps :: Bind AppsF where
  bind fa f = go fa where
    go = case _ of
      NoApp a -> f a
      l ~ r -> go l ~ go r
instance monadApps :: Monad AppsF

type Apps m a = AppsF (Expr m a)

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

_NoApp :: forall a. Lens.Prism' (AppsF a) a
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

noapplitG ::
  forall sym v all all' node ops.
    IsSymbol sym =>
    Row.Cons sym (Const v) all' all =>
  { unlayer :: node -> VariantF all node
  | ops
  } ->
  Proxy sym ->
  AppsF node ->
  Maybe v
noapplitG ops sym = noapplitG' ops sym >>> map unwrap

noapplitG' ::
  forall sym f all all' node ops.
    IsSymbol sym =>
    Row.Cons sym f all' all =>
  { unlayer :: node -> VariantF all node
  | ops
  } ->
  Proxy sym ->
  AppsF node ->
  Maybe (f node)
noapplitG' ops sym = Lens.preview _NoApp >=> ops.unlayer >>> VariantF.prj sym

noappG ::
  forall sym f all all' node ops.
    IsSymbol sym =>
    Row.Cons sym f all' all =>
  { unlayer :: node -> VariantF all node
  | ops
  } ->
  Proxy sym ->
  AppsF node ->
  Boolean
noappG ops sym = isJust <<< noapplitG' ops sym

appsG ::
  forall all' node ops.
  { unlayer :: node -> VariantF ( "App" :: AST.Pair | all' ) node
  , layer :: VariantF ( "App" :: AST.Pair | all' ) node -> node
  | ops
  } ->
  Lens.Iso' node (AppsF node)
appsG ops = Lens.iso fromExpr toExpr where
  toExpr = case _ of
    App f a -> ops.layer $ VariantF.inj (_S::S_ "App") $ AST.Pair (toExpr f) (toExpr a)
    NoApp e -> e
  fromExpr e =
    case VariantF.prj (_S::S_ "App") $ ops.unlayer e of
      Nothing -> NoApp e
      Just (AST.Pair fn arg) -> App (fromExpr fn) (fromExpr arg)

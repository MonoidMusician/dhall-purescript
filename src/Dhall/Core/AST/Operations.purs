module Dhall.Core.AST.Operations where

import Prelude

import Control.Monad.Free (hoistFree)
import Data.Bifunctor (lmap)
import Data.Functor.App (App(..))
import Data.Functor.Product (bihoistProduct)
import Data.Functor.Variant (VariantF)
import Data.Functor.Variant as VariantF
import Data.Map (Map)
import Data.Newtype (over)
import Data.Traversable (class Traversable, sequence, traverse)
import Dhall.Core.AST.Types (Expr(..), ExprLayerRow, embedW, projectW)
import Dhall.Core.StrMapIsh (class StrMapIsh)
import Dhall.Core.StrMapIsh as StrMapIsh
import Prim.Row as Row
import Type.Proxy (Proxy2)

-- Some general operations for the Expr AST
hoistExpr :: forall m m'. Functor m' => (m ~> m') -> Expr m ~> Expr m'
hoistExpr nat = over Expr $ hoistFree \a ->
  VariantF.expandOverMatch
    { "Project": lmap (over App nat)
    , "Record": ($) nat
    , "RecordLit": ($) nat
    , "Union": ($) nat
    , "UnionLit": (bihoistProduct identity nat $ _)
    } identity a

conv :: forall m m'. StrMapIsh m => StrMapIsh m' => Expr m ~> Expr m'
conv = hoistExpr StrMapIsh.conv

convTo :: forall m m'. StrMapIsh m => StrMapIsh m' => Proxy2 m' -> Expr m ~> Expr m'
convTo = hoistExpr <<< StrMapIsh.convTo

unordered :: forall m. StrMapIsh m => Expr m ~> Expr (Map String)
unordered = hoistExpr StrMapIsh.unordered

-- | Just a helper to handle recursive rewrites: top-down, requires explicit
-- | recursion for the cases that are handled by the rewrite.
rewriteTopDown :: forall r r' m a b.
  Row.Union r r' (ExprLayerRow m b) =>
  (
    (VariantF r (Expr m a) -> Expr m b) ->
    VariantF (ExprLayerRow m a) (Expr m a) ->
    Expr m b
  ) ->
  Expr m a -> Expr m b
rewriteTopDown rw1 = go where
  go expr = rw1 (map go >>> VariantF.expand >>> embedW) $ projectW expr

-- | Another recursion helper: bottom-up, recursion already happens before
-- | the rewrite gets ahold of it. Just follow the types.
rewriteBottomUp :: forall r r' m a b.
  Row.Union r r' (ExprLayerRow m b) =>
  (
    (VariantF r (Expr m b) -> Expr m b) ->
    VariantF (ExprLayerRow m a) (Expr m b) ->
    Expr m b
  ) ->
  Expr m a -> Expr m b
rewriteBottomUp rw1 = go where
  go expr = rw1 (VariantF.expand >>> embedW) $ go <$> projectW expr

rewriteTopDownA :: forall r r' m a b f. Applicative f =>
  Traversable (VariantF r) =>
  Row.Union r r' (ExprLayerRow m b) =>
  (
    (VariantF r (Expr m a) -> f (Expr m b)) ->
    VariantF (ExprLayerRow m a) (Expr m a) ->
    f (Expr m b)
  ) ->
  Expr m a -> f (Expr m b)
rewriteTopDownA rw1 = go where
  go expr = rw1 (traverse go >>> map (VariantF.expand >>> embedW)) $ projectW expr

rewriteBottomUpM :: forall r r' m a b f. Monad f => Traversable m =>
  Row.Union r r' (ExprLayerRow m b) =>
  (
    (VariantF r (Expr m b) -> (Expr m b)) ->
    VariantF (ExprLayerRow m a) (Expr m b) ->
    f (Expr m b)
  ) ->
  Expr m a -> f (Expr m b)
rewriteBottomUpM rw1 = go where
  go expr = rw1 (VariantF.expand >>> embedW) =<< traverse go (projectW expr)

rewriteBottomUpA :: forall r r' m a b f. Applicative f => Traversable m =>
  Row.Union r r' (ExprLayerRow m b) =>
  (
    (VariantF r (Expr m b) -> (Expr m b)) ->
    VariantF (ExprLayerRow m a) (f (Expr m b)) ->
    f (Expr m b)
  ) ->
  Expr m a -> f (Expr m b)
rewriteBottomUpA rw1 = go where
  go expr = rw1 (VariantF.expand >>> embedW) $ go <$> (projectW expr)

rewriteBottomUpA' :: forall r r' m a b f. Applicative f => Traversable m =>
  Traversable (VariantF r) =>
  Row.Union r r' (ExprLayerRow m b) =>
  (
    (VariantF r (f (Expr m b)) -> f (Expr m b)) ->
    VariantF (ExprLayerRow m a) (f (Expr m b)) ->
    f (Expr m b)
  ) ->
  Expr m a -> f (Expr m b)
rewriteBottomUpA' rw1 = go where
  go expr = rw1 (sequence >>> map (VariantF.expand >>> embedW)) $ go <$> (projectW expr)

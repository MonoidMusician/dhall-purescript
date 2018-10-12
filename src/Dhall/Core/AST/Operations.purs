module Dhall.Core.AST.Operations where

import Prelude

import Data.Functor.Variant (SProxy(..), VariantF)
import Data.Functor.Variant as VariantF
import Data.Tuple (Tuple(..), uncurry)
import Dhall.Core.AST.Types (Expr, ExprLayerRow, AllTheThings, embedW, projectW)
import Dhall.Core.AST.Types.Basics (CONST)
import Prim.Row as Row

-- | Just a helper to handle recursive rewrites: top-down, requires explicit
-- | recursion for the cases that are handled by the rewrite.
rewriteTopDown :: forall r r' m s t a b.
  Row.Union r r' (ExprLayerRow m t b) =>
  (
    (VariantF r (Expr m s a) -> Expr m t b) ->
    VariantF (ExprLayerRow m s a) (Expr m s a) ->
    Expr m t b
  ) ->
  Expr m s a -> Expr m t b
rewriteTopDown rw1 = go where
  go expr = rw1 (map go >>> VariantF.expand >>> embedW) $ projectW expr

-- | Another recursion helper: bottom-up, recursion already happens before
-- | the rewrite gets ahold of it. Just follow the types.
rewriteBottomUp :: forall r r' m s t a b.
  Row.Union r r' (ExprLayerRow m t b) =>
  (
    (VariantF r (Expr m t b) -> Expr m t b) ->
    VariantF (ExprLayerRow m s a) (Expr m t b) ->
    Expr m t b
  ) ->
  Expr m s a -> Expr m t b
rewriteBottomUp rw1 = go where
  go expr = rw1 (VariantF.expand >>> embedW) $ go <$> projectW expr

-- A helper to coalesce a tree of annotations into a single annotation on
-- a "real" AST node.
unfurl :: forall m s a. Monoid s =>
  Expr m s a -> Tuple s (VariantF (AllTheThings m ( "Embed" :: CONST a )) (Expr m s a))
unfurl e0 = go mempty e0 where
  go s = projectW >>>
    VariantF.on (SProxy :: SProxy "Note")
      (uncurry go)
      (Tuple s)

coalesce1 :: forall m s a. Monoid s => Expr m s a -> Expr m s a
coalesce1 e = case unfurl e of
  Tuple s v -> embedW $ VariantF.inj (SProxy :: SProxy "Note") $ Tuple s $
    embedW $ VariantF.expand v

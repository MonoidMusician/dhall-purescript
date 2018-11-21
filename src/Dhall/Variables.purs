module Dhall.Variables where

import Prelude

import Data.Eq (class Eq1)
import Data.Functor.Variant as VariantF
import Data.Newtype (unwrap)
import Dhall.Core.AST (Expr, LetF(..), Var(..), mkLam, mkLet, mkPi, mkVar)
import Dhall.Core.AST as AST
import Dhall.Core.AST.Types.Basics (BindingBody(..), S_, _S)

-- | `shift` is used by both normalization and type-checking to avoid variable
-- | capture by shifting variable indices
-- | For example, suppose that you were to normalize the following expression:
-- | ```dhall
-- | λ(a : Type) → λ(x : a) → (λ(y : a) → λ(x : a) → y) x
-- | ```
-- |
-- | If you were to substitute `y` with `x` without shifting any variable
-- | indices, then you would get the following incorrect result:
-- | ```dhall
-- | λ(a : Type) → λ(x : a) → λ(x : a) → x  -- Incorrect normalized form
-- | ```
-- |
-- | In order to substitute `x` in place of `y` we need to `shift` `x` by `1` in
-- | order to avoid being misinterpreted as the `x` bound by the innermost
-- | lambda.  If we perform that `shift` then we get the correct result:
-- | ```dhall
-- | λ(a : Type) → λ(x : a) → λ(x : a) → x@1
-- | ```
-- |
-- | As a more worked example, suppose that you were to normalize the following
-- | expression:
-- | ```dhall
-- |     λ(a : Type)
-- | →   λ(f : a → a → a)
-- | →   λ(x : a)
-- | →   λ(x : a)
-- | →   (λ(x : a) → f x x@1) x@1
-- | ```
-- |
-- | The correct normalized result would be:
-- | ```dhall
-- |     λ(a : Type)
-- | →   λ(f : a → a → a)
-- | →   λ(x : a)
-- | →   λ(x : a)
-- | →   f x@1 x
-- | ```
-- |
-- | The above example illustrates how we need to both increase and decrease
-- | variable indices as part of substitution:
-- | * We need to increase the index of the outer `x@1` to `x@2` before we
-- |   substitute it into the body of the innermost lambda expression in order
-- |   to avoid variable capture.  This substitution changes the body of the
-- |   lambda expression to `f x@2 x@1`
-- | * We then remove the innermost lambda and therefore decrease the indices of
-- |   both `x`s in `f x@2 x@1` to `f x@1 x` in order to reflect that one
-- |   less `x` variable is now bound within that scope
-- | Formally, `shift d (V x n) e` modifies the expression `e` by adding `d` to
-- | the indices of all variables named `x` whose indices are greater than
-- | `n + m`, where `m` is the number of bound variables of the same name
-- | within that scope
-- | In practice, `d` is always `1` or `-1` because we either:
-- | * increment variables by `1` to avoid variable capture during substitution
-- | * decrement variables by `1` when deleting lambdas after substitution
-- |
-- | `n` starts off at @0@ when substitution begins and increments every time we
-- | descend into a lambda or let expression that binds a variable of the same
-- | name in order to avoid shifting the bound variables by mistake.
shift :: forall m a. Int -> Var -> Expr m a -> Expr m a
shift d v@(V x n) = AST.rewriteTopDown $ identity
  >>> VariantF.on (_S::S_ "Var")
    (unwrap >>> \(V x' n') ->
      let n'' = if x == x' && n <= n' then n' + d else n'
      in mkVar (V x' n'')
    )
  >>> VariantF.on (_S::S_ "Lam")
    (\(BindingBody x' _A b) ->
      let
        _A' = shift d (V x n ) _A
        b'  = shift d (V x n') b
        n' = if x == x' then n + 1 else n
      in mkLam x' _A' b'
    )
  >>> VariantF.on (_S::S_ "Pi")
    (\(BindingBody x' _A _B) ->
      let
        _A' = shift d (V x n ) _A
        _B' = shift d (V x n') _B
        n' = if x == x' then n + 1 else n
      in mkPi x' _A' _B'
    )
  >>> VariantF.on (_S::S_ "Let")
    (\(LetF f mt r e) ->
      let
        n' = if x == f then n + 1 else n
        e' =  shift d (V x n') e
        mt' = shift d (V x n ) <$> mt
        r'  = shift d (V x n ) r
      in mkLet f mt' r' e'
    )

-- | Substitute all occurrences of a variable with an expression
-- | `subst x C B  ~  B[x := C]`
subst :: forall m a. Var -> Expr m a -> Expr m a -> Expr m a
subst v@(V x n) e = AST.rewriteTopDown $ identity
  >>> VariantF.on (_S::S_ "Var")
    (unwrap >>> \(V x' n') ->
      if x == x' && n == n' then e else mkVar (V x' n')
    )
  >>> VariantF.on (_S::S_ "Lam")
    (\(BindingBody y _A b) ->
      let
        _A' = subst (V x n )                  e  _A
        b'  = subst (V x n') (shift 1 (V y 0) e) b
        n'  = if x == y then n + 1 else n
      in mkLam y _A' b'
    )
  >>> VariantF.on (_S::S_ "Pi")
    (\(BindingBody y _A _B) ->
      let
        _A' = subst (V x n )                  e  _A
        _B' = subst (V x n') (shift 1 (V y 0) e) _B
        n'  = if x == y then n + 1 else n
      in mkPi y _A' _B'
    )
  >>> VariantF.on (_S::S_ "Let")
    (\(LetF f mt r b) ->
      let
        n' = if x == f then n + 1 else n
        b'  = subst (V x n') (shift 1 (V f 0) e) b
        mt' = subst (V x n) e <$> mt
        r'  = subst (V x n) e r
      in mkLet f mt' r' b'
    )

-- | The usual combination of subst and shift required for proper substitution.
shiftSubstShift :: forall m a. Var -> Expr m a -> Expr m a -> Expr m a
shiftSubstShift v a b = shift (-1) v (subst v (shift 1 v a) b)

shiftSubstShift0 :: forall m a. String ->  Expr m a -> Expr m a -> Expr m a
shiftSubstShift0 v = shiftSubstShift $ AST.V v 0

rename :: forall m a. Var -> Var -> Expr m a -> Expr m a
rename v0 v1 = shift (-1) v0 <<< subst v0 (mkVar v1) <<< shift 1 v1

-- | α-normalize an expression by renaming all variables to `"_"` and using
-- | De Bruijn indices to distinguish them
alphaNormalize :: forall m a. Expr m a -> Expr m a
alphaNormalize = AST.rewriteTopDown $ identity
  >>> VariantF.on (_S::S_ "Lam")
    (\(BindingBody x _A b_0) ->
      if x == "_" then mkLam x (alphaNormalize _A) (alphaNormalize b_0) else
      let
        b_4 = alphaNormalize $ rename (V x 0) (V "_" 0) b_0
      in mkLam "_" (alphaNormalize _A) b_4
    )
  >>> VariantF.on (_S::S_ "Pi")
    (\(BindingBody x _A _B_0) ->
      if x == "_" then mkPi x (alphaNormalize _A) (alphaNormalize _B_0) else
      let
        _B_3 = alphaNormalize $ rename (V x 0) (V "_" 0) _B_0
      in mkPi "_" (alphaNormalize _A) _B_3
    )
  >>> VariantF.on (_S::S_ "Let")
    (\(LetF x mt a b_0) ->
      if x == "_" then mkLet x (alphaNormalize <$> mt) (alphaNormalize a) (alphaNormalize b_0) else
      let
        b_3 = alphaNormalize $ rename (V x 0) (V "_" 0) b_0
      in mkLet "_" (alphaNormalize <$> mt) (alphaNormalize a) b_3
    )

-- | Detect if the given variable is free within the given expression
freeIn :: forall m a. Functor m => Eq1 m => Eq a => Var -> Expr m a -> Boolean
freeIn variable expression =
    shift 1 variable expression /= expression

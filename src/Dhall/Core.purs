module Dhall.Core ( module Dhall.Core ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Dhall.Core.AST (AllTheThings, BinOpF(..), BuiltinBinOps, BuiltinFuncs, BuiltinOps, BuiltinTypes, BuiltinTypes2, Const(..), Expr(..), ExprRow, FunctorThings, LetF(..), Literals, Literals2, MergeF(..), OrdMap, Pair(..), SimpleThings, Syntax, Terminals, TextLitF(..), Triplet(..), Var(..), _Expr, _ExprF, coalesce1, unfurl) as Dhall.Core
import Dhall.Core.AST (Expr, Var)
import Dhall.Core.Imports (Directory(..), File(..), FilePrefix(..), Import(..), ImportHashed(..), ImportMode(..), ImportType(..), prettyDirectory, prettyFile, prettyFilePrefix, prettyImport, prettyImportHashed, prettyImportType) as Dhall.Core

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
shift :: forall s a. Int -> Var -> Expr s a -> Expr s a
shift i v e = e

-- | Substitute all occurrences of a variable with an expression
-- | `subst x C B  ~  B[x := C]`
subst :: forall s a. Var -> Expr s a -> Expr s a -> Expr s a
subst v e1 e0 = e0

-- | α-normalize an expression by renaming all variables to `"_"` and using
-- | De Bruijn indices to distinguish them
alphaNormalize :: forall s a. Expr s a -> Expr s a
alphaNormalize = identity

-- | Reduce an expression to its normal form, performing beta reduction
-- | `normalize` does not type-check the expression.  You may want to type-check
-- | expressions before normalizing them since normalization can convert an
-- | ill-typed expression into a well-typed expression.
-- | However, `normalize` will not fail if the expression is ill-typed and will
-- | leave ill-typed sub-expressions unevaluated.
normalize :: forall s t a. Eq a => Expr s a -> Expr s {- t -} a
normalize = normalizeWith (const Nothing)

-- | This function is used to determine whether folds like `Natural/fold` or
-- | `List/fold` should be lazy or strict in their accumulator based on the type
-- | of the accumulator
-- |
-- | If this function returns `True`, then they will be strict in their
-- | accumulator since we can guarantee an upper bound on the amount of work to
-- | normalize the accumulator on each step of the loop.  If this function
-- | returns `False` then they will be lazy in their accumulator and only
-- | normalize the final result at the end of the fold
boundedType :: forall s a. Expr s a -> Boolean
boundedType _ = false

-- | Remove all `Note` constructors from an `Expr` (i.e. de-`Note`)
denote :: forall s t a. Expr s a -> Expr s {- t -} a
denote e = e

-- | Use this to wrap you embedded functions (see `normalizeWith`) to make them
-- | polymorphic enough to be used.
type Normalizer a = forall s. Expr s a -> Maybe (Expr s a)

{-| Reduce an expression to its normal form, performing beta reduction and applying
    any custom definitions.
    `normalizeWith` is designed to be used with function `typeWith`. The `typeWith`
    function allows typing of Dhall functions in a custom typing context whereas
    `normalizeWith` allows evaluating Dhall expressions in a custom context.
    To be more precise `normalizeWith` applies the given normalizer when it finds an
    application term that it cannot reduce by other means.
    Note that the context used in normalization will determine the properties of normalization.
    That is, if the functions in custom context are not total then the Dhall language, evaluated
    with those functions is not total either.
-}
normalizeWith :: forall s t a. Eq a => Normalizer a -> Expr s a -> Expr s {- t -} a
normalizeWith _ e = e

-- | Returns `true` if two expressions are α-equivalent and β-equivalent and
-- | `false` otherwise
judgmentallyEqual :: forall s t a. Eq (Expr s a) => Eq a => Expr s a -> Expr s {- t -} a -> Boolean
judgmentallyEqual eL0 eR0 = alphaBetaNormalize eL0 == alphaBetaNormalize eR0
  where
    alphaBetaNormalize :: Eq a => Expr s a -> Expr s a
    alphaBetaNormalize = alphaNormalize <<< normalize

-- | Check if an expression is in a normal form given a context of evaluation.
-- | Unlike `isNormalized`, this will fully normalize and traverse through the expression.
--
-- | It is much more efficient to use `isNormalized`.
isNormalizedWith :: forall s a. Eq (Expr s a) => Eq s => Eq a => Normalizer a -> Expr s a -> Boolean
isNormalizedWith ctx e = e == (normalizeWith ctx e)

-- | Quickly check if an expression is in normal form
isNormalized :: forall s a. Expr s a -> Boolean
isNormalized e = false

-- | Detect if the given variable is free within the given expression
freeIn :: forall s a. Eq (Expr s a) => Eq a => Var -> Expr s a -> Boolean
freeIn variable expression =
    shift 1 variable strippedExpression /= strippedExpression
  where
    strippedExpression = denote expression

-- | The set of reserved identifiers for the Dhall language
reservedIdentifiers :: Set String
reservedIdentifiers = Set.fromFoldable
  [ "let"
  , "in"
  , "Type"
  , "Kind"
  , "forall"
  , "Bool"
  , "True"
  , "False"
  , "merge"
  , "if"
  , "then"
  , "else"
  , "as"
  , "using"
  , "constructors"
  , "Natural"
  , "Natural/fold"
  , "Natural/build"
  , "Natural/isZero"
  , "Natural/even"
  , "Natural/odd"
  , "Natural/toInteger"
  , "Natural/show"
  , "Integer"
  , "Integer/show"
  , "Integer/toDouble"
  , "Double"
  , "Double/show"
  , "Text"
  , "List"
  , "List/build"
  , "List/fold"
  , "List/length"
  , "List/head"
  , "List/last"
  , "List/indexed"
  , "List/reverse"
  , "Optional"
  , "Optional/build"
  , "Optional/fold"
  ]

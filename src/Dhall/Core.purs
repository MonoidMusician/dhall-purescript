module Dhall.Core ( module Dhall.Core ) where

import Prelude

import Data.Foldable (all, any)
import Data.Functor.Mu (Mu(..))
import Data.Functor.Product (Product(..))
import Data.Functor.Variant (FProxy, SProxy(..), VariantF)
import Data.Const as ConstF
import Data.Functor.Variant as VariantF
import Data.Identity (Identity(..))
import Data.HeytingAlgebra (tt, ff)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens as Lens
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Maybe.First (First)
import Data.Newtype (class Newtype, under, unwrap, wrap)
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Data.Variant as Variant
import Dhall.Core.AST (AllTheThings, BinOpF(..), BuiltinBinOps, BuiltinFuncs, BuiltinOps, BuiltinTypes, BuiltinTypes2, Const(..), Expr(..), ExprRow, FunctorThings, LetF(..), Literals, Literals2, MergeF(..), OrdMap, Pair(..), SimpleThings, Syntax, Terminals, TextLitF(..), Triplet(..), Var(..), _Expr, _ExprF, coalesce1, unfurl) as Dhall.Core
import Dhall.Core.AST (Expr(..), LetF(..), Var(..), mkLam, mkLet, mkPi, mkVar)
import Dhall.Core.AST as AST
import Dhall.Core.Imports (Directory(..), File(..), FilePrefix(..), Import(..), ImportHashed(..), ImportMode(..), ImportType(..), prettyDirectory, prettyFile, prettyFilePrefix, prettyImport, prettyImportHashed, prettyImportType) as Dhall.Core
import Unsafe.Coerce (unsafeCoerce)

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
shift d v@(V x n) = go where
  go (Expr (In expr)) =
    ( ( map (under Expr go)
    >>> VariantF.expand >>> In >>> Expr
      )
    # VariantF.on (SProxy :: SProxy "SimpleThings")
      ( (>>>) unwrap
      $ ( Variant.expand
      >>> wrap
      >>> VariantF.inj (SProxy :: SProxy "SimpleThings")
      >>> In >>> Expr
        )
      # Variant.on (SProxy :: SProxy "Var")
        (\(V x' n') ->
          let n'' = if x == x' && n <= n' then n' + d else n'
          in mkVar (V x' n'')
        )
      )
    # VariantF.on (SProxy :: SProxy "Lam")
      (\(Product (Tuple (Tuple x' _A) (Identity b))) ->
        let
          _A' = shift d (V x n ) <<< Expr $ _A
          b'  = shift d (V x n') <<< Expr $ b
          n' = if x == x' then n + 1 else n
        in mkLam x' _A' b'
      )
    # VariantF.on (SProxy :: SProxy "Pi")
      (\(Product (Tuple (Tuple x' _A) (Identity _B))) ->
        let
          _A' = shift d (V x n ) <<< Expr $ _A
          _B' = shift d (V x n') <<< Expr $ _B
          n' = if x == x' then n + 1 else n
        in mkPi x' _A' _B'
      )
    # VariantF.on (SProxy :: SProxy "Let")
      (\(LetF f mt r e) ->
        let
          n' = if x == f then n + 1 else n
          e' =  shift d (V x n') <<< Expr $ e
          mt' = shift d (V x n ) <<< Expr <$> mt
          r'  = shift d (V x n ) <<< Expr $ r
        in mkLet f mt' r' e'
      )
    ) expr

-- | Substitute all occurrences of a variable with an expression
-- | `subst x C B  ~  B[x := C]`
subst :: forall s a. Var -> Expr s a -> Expr s a -> Expr s a
subst v@(V x n) e = go where
  go (Expr (In expr)) =
    ( ( map (under Expr go)
    >>> VariantF.expand >>> In >>> Expr
      )
    # VariantF.on (SProxy :: SProxy "SimpleThings")
      ( (>>>) unwrap
      $ ( Variant.expand
      >>> wrap
      >>> VariantF.inj (SProxy :: SProxy "SimpleThings")
      >>> In >>> Expr
        )
      # Variant.on (SProxy :: SProxy "Var")
        (\(V x' n') ->
          if x == x' && n == n' then e else mkVar (V x' n')
        )
      )
    # VariantF.on (SProxy :: SProxy "Lam")
      (\(Product (Tuple (Tuple y _A) (Identity b))) ->
        let
          _A' = subst (V x n )                  e  <<< Expr $ _A
          b'  = subst (V x n') (shift 1 (V y 0) e) <<< Expr $ b
          n'  = if x == y then n + 1 else n
        in mkLam y _A' b'
      )
    # VariantF.on (SProxy :: SProxy "Pi")
      (\(Product (Tuple (Tuple y _A) (Identity _B))) ->
        let
          _A' = subst (V x n )                  e  <<< Expr $ _A
          _B' = subst (V x n') (shift 1 (V y 0) e) <<< Expr $ _B
          n'  = if x == y then n + 1 else n
        in mkPi y _A' _B'
      )
    # VariantF.on (SProxy :: SProxy "Let")
      (\(LetF f mt r b) ->
        let
          n' = if x == f then n + 1 else n
          b'  = subst (V x n') (shift 1 (V f 0) e) <<< Expr $ b
          mt' = subst (V x n) e <<< Expr <$> mt
          r'  = subst (V x n) e <<< Expr $ r
        in mkLet f mt' r' b'
      )
    ) expr

-- | α-normalize an expression by renaming all variables to `"_"` and using
-- | De Bruijn indices to distinguish them
alphaNormalize :: forall s a. Expr s a -> Expr s a
alphaNormalize = go where
  v_0 = mkVar (V "_" 0)
  go (Expr (In expr)) =
    ( ( map (go >>> unwrap)
    >>> VariantF.expand >>> In >>> Expr
      )
    # VariantF.on (SProxy :: SProxy "Lam")
      (\(Product (Tuple (Tuple x _A) (Identity b_0))) ->
        let
          v_1 = shift 1 (V x 0) v_0
          b_1 = subst (V x 0) v_1 b_0
          b_2 = shift (-1) (V x 0) b_1
          b_3 = alphaNormalize b_2
        in mkLam "_" (go _A) b_3
      )
    # VariantF.on (SProxy :: SProxy "Pi")
      (\(Product (Tuple (Tuple x _A) (Identity _B_0))) ->
        let
          v_1 = shift 1 (V x 0) v_0
          _B_1 = subst (V x 0) v_1 _B_0
          _B_2 = shift (-1) (V x 0) _B_1
          _B_3 = alphaNormalize _B_2
        in mkPi "_" (go _A) _B_3
      )
    # VariantF.on (SProxy :: SProxy "Let")
      (\(LetF x mt a b_0) ->
        let
          v_1 = shift 1 (V x 0) v_0
          b_1 = subst (V x 0) v_1 b_0
          b_2 = shift (-1) (V x 0) b_1
          b_3 = alphaNormalize b_2
        in mkLet "_" (go <$> mt) (go a) b_3
      )
    ) (Expr <$> expr)

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
denote :: forall s t a. Expr s a -> Expr t a
denote (Expr (In e)) =
  ( ( map (under Expr denote)
  >>> VariantF.expand
  >>> In >>> Expr
    )
  # VariantF.on (SProxy :: SProxy "Note")
    (\(Tuple _ e') -> denote (Expr e'))
  ) e

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
judgmentallyEqual :: forall s t a. Eq s => Eq a => Expr s a -> Expr s {- t -} a -> Boolean
judgmentallyEqual eL0 eR0 = alphaBetaNormalize eL0 == alphaBetaNormalize eR0
  where
    alphaBetaNormalize :: Eq a => Expr s a -> Expr s a
    alphaBetaNormalize = alphaNormalize <<< normalize

-- | Check if an expression is in a normal form given a context of evaluation.
-- | Unlike `isNormalized`, this will fully normalize and traverse through the expression.
--
-- | It is much more efficient to use `isNormalized`.
isNormalizedWith :: forall s a. Eq s => Eq a => Normalizer a -> Expr s a -> Boolean
isNormalizedWith ctx e = e == (normalizeWith ctx e)

type Preview' a b = Lens.Fold (First b) a a b b

-- | Quickly check if an expression is in normal form
isNormalized :: forall s a. Eq s => Eq a => Expr s a -> Boolean
isNormalized (Expr e0) = go e0 where
  onP :: forall e v r.
    Preview' e v ->
    (v -> r) -> (e -> r) ->
    e -> r
  onP p this other e = case Lens.preview p e of
    Just v -> this v
    _ -> other e

  onP2 :: forall e e' v v' r.
    Preview' e v -> Preview' e' v' ->
    (v -> v' -> r) -> (e -> e' -> r) ->
    e -> e' -> r
  onP2 p p' this other e e' = case Lens.preview p e, Lens.preview p' e' of
    Just v, Just v' -> this v v'
    _, _ -> other e e'

  appFn :: forall r o.
    Lens.Traversal' (VariantF ( "App" :: FProxy AST.Pair | r ) o) o
  appFn = AST._App <<< prop (SProxy :: SProxy "fn")
  appFn' :: forall p r o o' o''.
    Lens.Wander p =>
    Newtype o o' =>
    Lens.Optic' p o' o'' ->
    Lens.Optic' p (VariantF ( "App" :: FProxy AST.Pair | r ) o) o''
  appFn' p = appFn <<< _Newtype <<< p
  appArg :: forall r o.
    Lens.Traversal' (VariantF ( "App" :: FProxy AST.Pair | r ) o) o
  appArg = AST._App <<< prop (SProxy :: SProxy "arg")
  appArg' :: forall p r o o' o''.
    Lens.Wander p =>
    Newtype o o' =>
    Lens.Optic' p o' o'' ->
    Lens.Optic' p (VariantF ( "App" :: FProxy AST.Pair | r ) o) o''
  appArg' p = appArg <<< _Newtype <<< p

  seq :: forall b c.
    Preview' b Unit ->
    Preview' b c ->
    Preview' b c
  seq p1 p2 f = wrap \a ->
    case unwrap (unwrap (p1 (wrap (wrap <<< Just))) a) of
      Nothing -> mempty
      Just _ -> unwrap (p2 f) a

  getArg :: forall r o o' e.
    Newtype o o' =>
    Preview' o' (ConstF.Const Unit e) ->
    Preview' (VariantF ( "App" :: FProxy AST.Pair | r ) o) o
  getArg p = seq (appFn' (unsafeCoerce p)) appArg

  ain't :: forall f b. Lens.APrism' (f (Mu f)) b -> Mu f -> Boolean
  ain't p = not Lens.is p <<< unwrap

  go :: Mu (VariantF (AST.ExprRow s a)) -> Boolean
  go (In e) = if not all go e then false else
    ( tt
    # onP AST._Note ff
    # onP AST._BoolAnd
      (all (ain't AST._BoolLit))
    # onP AST._BoolOr
      (all (ain't AST._BoolLit))
    # onP AST._BoolEQ
      (any (ain't AST._BoolLit))
    # onP AST._BoolNE
      (any (ain't AST._BoolLit))
    # onP AST._BoolIf
      (\(AST.Triplet b t f) ->
        let checkLit = ain't AST._BoolLit
        in checkLit b
        && not (Lens.is AST._BoolLit_True  (unwrap t)
             && Lens.is AST._BoolLit_False (unwrap f))
        && not judgmentallyEqual (Expr t) (Expr f)
      )
    # onP AST._NaturalPlus
      (\(AST.Pair l r) ->
        let
          checkLit = ain't AST._NaturalLit
          check_0 = ain't AST._NaturalLit_0
        in check_0 l && check_0 r
        && (checkLit l || checkLit r)
      )
    # onP AST._NaturalTimes
      (\(AST.Pair l r) ->
        let
          checkLit = ain't AST._NaturalLit
          check_0 = ain't AST._NaturalLit_0
          check_1 = ain't AST._NaturalLit_1
        in check_0 l && check_0 r
        && check_1 l && check_1 r
        && (checkLit l || checkLit r)
      )
    # onP AST._ListAppend
      (\(AST.Pair l r) ->
        let
          checkLit = ain't AST._ListLit
          check_empty v = case Lens.preview AST._ListLit (unwrap v) of
            Just { values: [] } -> false
            _ -> true
        in check_empty l && check_empty r
        && (checkLit l || checkLit r)
      )
    # onP AST._Combine
      (\(AST.Pair l r) ->
        let
          checkLit = ain't AST._RecordLit
          check_empty = ain't AST._RecordLit_empty
        in check_empty l && check_empty r
        && (checkLit l || checkLit r)
      )
    # onP AST._CombineTypes
      (\(AST.Pair l r) ->
        let
          checkLit = ain't AST._Record
          check_empty = ain't AST._Record_empty
        in check_empty l && check_empty r
        && (checkLit l || checkLit r)
      )
    # onP AST._Prefer
      (\(AST.Pair l r) ->
        let
          checkLit = ain't AST._RecordLit
          check_empty = ain't AST._RecordLit_empty
        in check_empty l && check_empty r
        && (checkLit l || checkLit r)
      )
    # onP AST._Constructors (ain't AST._Union)
    # onP AST._App \{ fn, arg } ->
      ( tt
      -- substitution
      # onP2 AST._Lam identity ff
      -- build/fold fusion for `List`
      -- App (App ListBuild _) (App (App ListFold _) e')
      # onP2 (appFn' AST._ListBuild) (getArg (appFn' AST._ListFold)) ff
      -- build/fold fusion for `Natural`
      -- App NaturalBuild (App NaturalFold e')
      # onP2 AST._NaturalBuild (getArg AST._NaturalFold) ff
      -- build/fold fusion for `Optional`
      -- App (App OptionalBuild _) (App (App OptionalFold _) e')
      # onP2 (appFn' AST._OptionalBuild) (getArg (appFn' AST._OptionalFold)) ff
      ) (unwrap fn) (unwrap arg)
    ) e

-- | Detect if the given variable is free within the given expression
freeIn :: forall s a. Eq a => Var -> Expr s a -> Boolean
freeIn variable expression =
    shift 1 variable strippedExpression /= strippedExpression
  where
    strippedExpression :: Expr Void a
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

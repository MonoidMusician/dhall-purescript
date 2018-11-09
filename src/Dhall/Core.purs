module Dhall.Core ( module Dhall.Core ) where

import Prelude

import Data.Const as ConstF
import Data.Eq (class Eq1)
import Data.Function (on)
import Data.Functor.Variant (SProxy(..), VariantF)
import Data.Functor.Variant as VariantF
import Data.FunctorWithIndex (mapWithIndex)
import Data.Int (even, toNumber)
import Data.Lens as Lens
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Maybe.First (First)
import Data.Natural (natToInt)
import Data.Newtype (class Newtype, unwrap)
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (snd)
import Dhall.Core.AST (AllTheThings, BuiltinBinOps, BuiltinFuncs, BuiltinOps, BuiltinTypes, BuiltinTypes2, Const(..), Expr(..), ExprRow, FunctorThings, LetF(..), Literals, Literals2, MergeF(..), Pair(..), SimpleThings, Syntax, Terminals, TextLitF(..), Triplet(..), Var(..), _Expr, _ExprF, coalesce1, unfurl) as Dhall.Core
import Dhall.Core.AST (Expr, LetF(..), Var(..), mkLam, mkLet, mkPi, mkVar, projectW)
import Dhall.Core.AST.Types.Basics (BindingBody(..))
import Dhall.Core.AST as AST
import Dhall.Core.Imports (Directory(..), File(..), FilePrefix(..), Import(..), ImportHashed(..), ImportMode(..), ImportType(..), prettyDirectory, prettyFile, prettyFilePrefix, prettyImport, prettyImportHashed, prettyImportType) as Dhall.Core
import Dhall.Core.StrMapIsh (class StrMapIsh)
import Dhall.Core.StrMapIsh as StrMapIsh
import Matryoshka (class Recursive, project)
import Unsafe.Coerce (unsafeCoerce)

type S_ = SProxy
_s = SProxy :: forall s. S_ s

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
shift :: forall m s a. Int -> Var -> Expr m s a -> Expr m s a
shift d v@(V x n) = AST.rewriteTopDown $ identity
  >>> VariantF.on (_s::S_ "Var")
    (unwrap >>> \(V x' n') ->
      let n'' = if x == x' && n <= n' then n' + d else n'
      in mkVar (V x' n'')
    )
  >>> VariantF.on (_s::S_ "Lam")
    (\(BindingBody x' _A b) ->
      let
        _A' = shift d (V x n ) _A
        b'  = shift d (V x n') b
        n' = if x == x' then n + 1 else n
      in mkLam x' _A' b'
    )
  >>> VariantF.on (_s::S_ "Pi")
    (\(BindingBody x' _A _B) ->
      let
        _A' = shift d (V x n ) _A
        _B' = shift d (V x n') _B
        n' = if x == x' then n + 1 else n
      in mkPi x' _A' _B'
    )
  >>> VariantF.on (_s::S_ "Let")
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
subst :: forall m s a. Var -> Expr m s a -> Expr m s a -> Expr m s a
subst v@(V x n) e = AST.rewriteTopDown $ identity
  >>> VariantF.on (_s::S_ "Var")
    (unwrap >>> \(V x' n') ->
      if x == x' && n == n' then e else mkVar (V x' n')
    )
  >>> VariantF.on (_s::S_ "Lam")
    (\(BindingBody y _A b) ->
      let
        _A' = subst (V x n )                  e  _A
        b'  = subst (V x n') (shift 1 (V y 0) e) b
        n'  = if x == y then n + 1 else n
      in mkLam y _A' b'
    )
  >>> VariantF.on (_s::S_ "Pi")
    (\(BindingBody y _A _B) ->
      let
        _A' = subst (V x n )                  e  _A
        _B' = subst (V x n') (shift 1 (V y 0) e) _B
        n'  = if x == y then n + 1 else n
      in mkPi y _A' _B'
    )
  >>> VariantF.on (_s::S_ "Let")
    (\(LetF f mt r b) ->
      let
        n' = if x == f then n + 1 else n
        b'  = subst (V x n') (shift 1 (V f 0) e) b
        mt' = subst (V x n) e <$> mt
        r'  = subst (V x n) e r
      in mkLet f mt' r' b'
    )

-- | α-normalize an expression by renaming all variables to `"_"` and using
-- | De Bruijn indices to distinguish them
alphaNormalize :: forall m s a. Expr m s a -> Expr m s a
alphaNormalize = AST.rewriteTopDown $ identity
  >>> VariantF.on (_s::S_ "Lam")
    (\(BindingBody x _A b_0) ->
      if x == "_" then mkLam x (alphaNormalize _A) (alphaNormalize b_0) else
      let
        b_1 = shift 1 (V "_" 0) b_0
        b_2 = subst (V x 0) (mkVar (V "_" 0)) b_1
        b_3 = shift (-1) (V x 0) b_2
        b_4 = alphaNormalize b_3
      in mkLam "_" (alphaNormalize _A) b_4
    )
  >>> VariantF.on (_s::S_ "Pi")
    (\(BindingBody x _A _B_0) ->
      if x == "_" then mkPi x (alphaNormalize _A) (alphaNormalize _B_0) else
      let
        _B_1 = shift 1 (V "_" 0) _B_0
        _B_2 = subst (V x 0) (mkVar (V "_" 0)) _B_1
        _B_3 = shift (-1) (V x 0) _B_2
        _B_4 = alphaNormalize _B_3
      in mkPi "_" (alphaNormalize _A) _B_3
    )
  >>> VariantF.on (_s::S_ "Let")
    (\(LetF x mt a b_0) ->
      if x == "_" then mkLet x (alphaNormalize <$> mt) (alphaNormalize a) (alphaNormalize b_0) else
      let
        b_1 = shift 1 (V "_" 0) b_0
        b_2 = subst (V x 0) (mkVar (V "_" 0)) b_1
        b_3 = shift (-1) (V x 0) b_2
        b_4 = alphaNormalize b_3
      in mkLet "_" (alphaNormalize <$> mt) (alphaNormalize a) b_3
    )

-- | Reduce an expression to its normal form, performing beta reduction
-- | `normalize` does not type-check the expression.  You may want to type-check
-- | expressions before normalizing them since normalization can convert an
-- | ill-typed expression into a well-typed expression.
-- | However, `normalize` will not fail if the expression is ill-typed and will
-- | leave ill-typed sub-expressions unevaluated.
normalize :: forall m s t a. StrMapIsh m => Eq a => Expr m s a -> Expr m t a
normalize = normalizeWith (const (const Nothing))

-- | This function is used to determine whether folds like `Natural/fold` or
-- | `List/fold` should be lazy or strict in their accumulator based on the type
-- | of the accumulator
-- |
-- | If this function returns `True`, then they will be strict in their
-- | accumulator since we can guarantee an upper bound on the amount of work to
-- | normalize the accumulator on each step of the loop.  If this function
-- | returns `False` then they will be lazy in their accumulator and only
-- | normalize the final result at the end of the fold
boundedType :: forall m s a. Expr m s a -> Boolean
boundedType _ = false

-- | Remove all `Note` constructors from an `Expr` (i.e. de-`Note`)
denote :: forall m s t a. Functor m => Expr m s a -> Expr m t a
denote = AST.rewriteBottomUp (VariantF.on (_s::S_ "Note") snd)

-- | Use this to wrap you embedded functions (see `normalizeWith`) to make them
-- | polymorphic enough to be used.
type Normalizer a = forall m s. Expr m s a -> Expr m s a -> Maybe (Expr m s a)

newtype WrappedNormalizer a = WrappedNormalizer (Normalizer a)
-- not Alt, because it is not a covariant functor
instance semigroupWrappedNormalizer :: Semigroup (WrappedNormalizer a) where
  append (WrappedNormalizer n) (WrappedNormalizer m) = WrappedNormalizer \fn arg ->
    case n fn arg of
      Just r -> Just r
      Nothing -> m fn arg
instance monoidWrappedNormalizer :: Monoid (WrappedNormalizer a) where
  mempty = WrappedNormalizer \_ _ -> Nothing

type Preview' a b = Lens.Fold (First b) a a b b

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
normalizeWith :: forall m s t a. StrMapIsh m => Eq a => Normalizer a -> Expr m s a -> Expr m t a
normalizeWith ctx = AST.rewriteBottomUp rules where
  onP :: forall e v r.
    Preview' e v ->
    (v -> r) -> (e -> r) ->
    e -> r
  onP p this other e = case Lens.preview p e of
    Just v -> this v
    _ -> other e

  previewE :: forall ft f o' e.
    Recursive ft f =>
    Newtype (f ft) o' =>
    Preview' o' e ->
    ft -> Maybe e
  previewE p = Lens.preview p <<< unwrap <<< project
  unPair ::  forall ft f o' e r.
    Recursive ft f =>
    Newtype (f ft) o' =>
    Preview' o' e ->
    (ft -> ft -> Maybe e -> Maybe e -> r) ->
    AST.Pair ft ->
    r
  unPair p f (AST.Pair l r) = f l r (previewE p l) (previewE p r)
  unPairN ::  forall ft f o' e e' r.
    Recursive ft f =>
    Newtype (f ft) o' =>
    Newtype e e' =>
    Preview' o' e ->
    (ft -> ft -> Maybe e' -> Maybe e' -> r) ->
    AST.Pair ft ->
    r
  unPairN p = unPair (unsafeCoerce p)

  -- The companion to judgmentallyEqual for terms that are already
  -- normalized recursively from this
  judgEq = eq `on` (alphaNormalize >>> unsafeCoerce :: Expr m t a -> Expr m Void a)

  rules = identity
    >>> VariantF.on (_s::S_ "BoolAnd")
      (unPairN AST._BoolLit \l r -> case _, _ of
        Just true, _ -> r -- (l = True) && r -> r
        Just false, _ -> l -- (l = False) && r -> (l = False)
        _, Just false -> r -- l && (r = False) -> (r = False)
        _, Just true -> l -- l && (r = True) -> l
        _, _ ->
          if judgEq (l) (r)
          then l
          else AST.mkBoolAnd (l) (r)
      )
    >>> VariantF.on (_s::S_ "BoolOr")
      (unPairN AST._BoolLit \l r -> case _, _ of
        Just true, _ -> l -- (l = True) || r -> (l = True)
        Just false, _ -> r -- (l = False) || r -> r
        _, Just false -> l -- l || (r = False) -> l
        _, Just true -> r -- l || (r = True) -> (r = True)
        _, _ ->
          if judgEq (l) (r)
          then l
          else AST.mkBoolOr (l) (r)
      )
    >>> VariantF.on (_s::S_ "BoolEQ")
      (unPairN AST._BoolLit \l r -> case _, _ of
        Just a, Just b -> AST.mkBoolLit (a == b)
        _, _ ->
          if judgEq (l) (r)
          then AST.mkBoolLit true
          else AST.mkBoolEQ (l) (r)
      )
    >>> VariantF.on (_s::S_ "BoolNE")
      (unPairN AST._BoolLit \l r -> case _, _ of
        Just a, Just b -> AST.mkBoolLit (a /= b)
        _, _ ->
          if judgEq (l) (r)
          then AST.mkBoolLit false
          else AST.mkBoolNE (l) (r)
      )
    >>> VariantF.on (_s::S_ "BoolIf")
      (\(AST.Triplet b t f) ->
        let p = AST._BoolLit <<< _Newtype in
        case previewE p b of
          Just true -> t
          Just false -> f
          Nothing ->
            case previewE p t, previewE p f of
              Just true, Just false -> b
              _, _ ->
                if judgEq (t) (f)
                  then t
                  else AST.mkBoolIf (b) (t) (f)
      )
    >>> VariantF.on (_s::S_ "NaturalPlus")
      (unPairN AST._NaturalLit \l r -> case _, _ of
        Just a, Just b -> AST.mkNaturalLit (a + b)
        Just a, _ | a == zero -> r
        _, Just b | b == zero -> l
        _, _ -> AST.mkNaturalPlus (l) (r)
      )
    >>> VariantF.on (_s::S_ "NaturalTimes")
      (unPairN AST._NaturalLit \l r -> case _, _ of
        Just a, Just b -> AST.mkNaturalLit (a * b)
        Just a, _ | a == zero -> l
        _, Just b | b == zero -> r
        Just a, _ | a == one -> r
        _, Just b | b == one -> l
        _, _ -> AST.mkNaturalTimes (l) (r)
      )
    >>> VariantF.on (_s::S_ "ListAppend")
      (unPair AST._ListLit \l r -> case _, _ of
        Just { ty, values: a }, Just { values: b } ->
          AST.mkListLit ty (a <> b)
        Just { values: [] }, _ -> r
        _, Just { values: [] } -> l
        _, _ -> AST.mkListAppend (l) (r)
      )
    >>> VariantF.on (_s::S_ "Combine")
      (let
        decide = unPair AST._RecordLit \l r -> case _, _ of
          Just a, Just b -> AST.mkRecordLit $
            StrMapIsh.unionWith (\x y -> decide (AST.Pair x y)) a b
          Just a, _ | StrMapIsh.isEmpty a -> r
          _, Just b | StrMapIsh.isEmpty b -> l
          _, _ -> AST.mkCombine (l) (r)
      in decide)
    >>> VariantF.on (_s::S_ "CombineTypes")
      (let
        decide = unPair AST._Record \l r -> case _, _ of
          Just a, Just b -> AST.mkRecord $
            StrMapIsh.unionWith (\x y -> decide (AST.Pair x y)) a b
          Just a, _ | StrMapIsh.isEmpty a -> r
          _, Just b | StrMapIsh.isEmpty b -> l
          _, _ -> AST.mkCombineTypes (l) (r)
      in decide)
    >>> VariantF.on (_s::S_ "Prefer")
      (let
        decide = unPair AST._RecordLit \l r -> case _, _ of
          Just a, Just b -> AST.mkRecordLit $
            StrMapIsh.unionWith const a b
          Just a, _ | StrMapIsh.isEmpty a -> r
          _, Just b | StrMapIsh.isEmpty b -> l
          _, _ -> AST.mkPrefer (l) (r)
      in decide)
    >>> VariantF.on (_s::S_ "Constructors")
      (unwrap >>> \e' -> case previewE AST._Union e' of
        Just kts -> AST.mkRecord $ kts # mapWithIndex \k t_ ->
          AST.mkLam k (t_) $ AST.mkUnionLit k (AST.mkVar (AST.V k 0)) $
            (fromMaybe <*> StrMapIsh.delete k) kts
        Nothing -> AST.mkConstructors (e')
      )
    >>> onP AST._Let
      (\{ var, ty, value, body } ->
        let v = AST.V var 0 in normalizeWith ctx $
        shift (-1) v (subst v (shift 1 v (value)) (body))
      )
    >>> VariantF.on (_s::S_ "Note") snd
    -- composing with <<< gives this case priority
    >>> identity <<< onP AST._App \{ fn, arg } ->
      onP AST._Lam
        (\{ var: x, body } ->
          let
            v = AST.V x 0
          in normalizeWith ctx $ shift (-1) v $
            subst v (shift 1 v (arg)) (body)
        ) <@> projectW fn $ \_ ->
      case Lens.view apps (fn), Lens.view apps (arg) of
        -- build/fold fusion for `List`
        -- App (App ListBuild _) (App (App ListFold _) e') -> loop e'
        App listbuild _, App (App listfold _) e'
          | noapp AST._ListBuild listbuild
          , noapp AST._ListFold listfold ->
            Lens.review apps e'
        -- build/fold fusion for `Natural`
        -- App NaturalBuild (App NaturalFold e') -> loop e'
        naturalbuild, App naturalfold e'
          | noapp AST._NaturalBuild naturalbuild
          , noapp AST._NaturalFold naturalfold ->
            Lens.review apps e'
        -- build/fold fusion for `Optional`
        -- App (App OptionalBuild _) (App (App OptionalFold _) e') -> loop e'
        App optionalbuild _, App (App optionalfold _) e'
          | noapp AST._OptionalBuild optionalbuild
          , noapp AST._OptionalFold optionalfold ->
            Lens.review apps e'

        naturalbuild, g
          | noapp AST._NaturalBuild naturalbuild ->
            let
              zero_ = AST.mkNaturalLit zero
              succ_ = AST.mkLam "x" AST.mkNatural $
                AST.mkNaturalPlus (AST.mkVar (AST.V "x" 0)) $ AST.mkNaturalLit one
              g' = Lens.review apps g
            in normalizeWith ctx $
              AST.mkApp (AST.mkApp (AST.mkApp g' AST.mkNatural) succ_) zero_
        naturaliszero, naturallit
          | noapp AST._NaturalIsZero naturaliszero
          , Just n <- noapplit AST._NaturalLit naturallit ->
            AST.mkBoolLit (n == zero)
        naturaleven, naturallit
          | noapp AST._NaturalEven naturaleven
          , Just n <- noapplit AST._NaturalLit naturallit ->
            AST.mkBoolLit (even (natToInt n))
        naturalodd, naturallit
          | noapp AST._NaturalOdd naturalodd
          , Just n <- noapplit AST._NaturalLit naturallit ->
            AST.mkBoolLit (not even (natToInt n))
        naturaltointeger, naturallit
          | noapp AST._NaturalToInteger naturaltointeger
          , Just n <- noapplit AST._NaturalLit naturallit ->
            AST.mkIntegerLit (natToInt n)
        naturalshow, naturallit
          | noapp AST._NaturalShow naturalshow
          , Just n <- noapplit AST._NaturalLit naturallit ->
            AST.mkTextLit (AST.TextLit (show n))
        integershow, integerlit
          | noapp AST._IntegerShow integershow
          , Just n <- noapplit AST._IntegerLit integerlit ->
            let s = if n >= 0 then "+" else "" in
            AST.mkTextLit (AST.TextLit (s <> show n))
        integertodouble, integerlit
          | noapp AST._IntegerToDouble integertodouble
          , Just n <- noapplit AST._IntegerLit integerlit ->
            AST.mkDoubleLit (toNumber n)
        doubleshow, doublelit
          | noapp AST._DoubleShow doubleshow
          , Just n <- noapplit AST._DoubleLit doublelit ->
            AST.mkTextLit (AST.TextLit (show n))
        _, _ ->
          AST.mkApp (fn) (arg)

-- Little ADT to make destructuring applications easier for normalization
data Apps m s a = App (Apps m s a) (Apps m s a) | NoApp (Expr m s a)

noapplit :: forall m s a v.
  Lens.Prism'
    (VariantF (AST.ExprLayerRow m s a) (Expr m s a))
    (ConstF.Const v (Expr m s a)) ->
  Apps m s a ->
  Maybe v
noapplit p = Lens.preview (_NoApp <<< AST._E p <<< _Newtype)

noapp :: forall f m s a. Functor f =>
  Lens.Prism'
    (VariantF (AST.ExprLayerRow m s a) (Expr m s a))
    (f (Expr m s a)) ->
  Apps m s a ->
  Boolean
noapp p = Lens.is (_NoApp <<< AST._E p)

_NoApp :: forall m s a. Lens.Prism' (Apps m s a) (Expr m s a)
_NoApp = Lens.prism' NoApp case _ of
  NoApp e -> Just e
  _ -> Nothing

apps :: forall m s a. Lens.Iso' (Expr m s a) (Apps m s a)
apps = Lens.iso fromExpr toExpr where
  toExpr = case _ of
    App f a -> AST.mkApp (toExpr f) (toExpr a)
    NoApp e -> e
  fromExpr e =
    case Lens.preview (AST._E (AST._ExprFPrism (_s::S_ "App"))) e of
      Nothing -> NoApp e
      Just (AST.Pair fn arg) -> App (fromExpr fn) (fromExpr arg)

-- | Returns `true` if two expressions are α-equivalent and β-equivalent and
-- | `false` otherwise
judgmentallyEqual :: forall m s t a. StrMapIsh m => Eq a => Expr m s a -> Expr m t a -> Boolean
judgmentallyEqual eL0 eR0 = alphaBetaNormalize eL0 == alphaBetaNormalize eR0
  where
    alphaBetaNormalize :: forall st. Eq a => Expr m st a -> Expr m Void a
    alphaBetaNormalize = alphaNormalize <<< normalize

-- | Check if an expression is in a normal form given a context of evaluation.
-- | Unlike `isNormalized`, this will fully normalize and traverse through the expression.
--
-- | It is much more efficient to use `isNormalized`.
isNormalized :: forall m s a. StrMapIsh m => Eq s => Eq a => Expr m s a -> Boolean
isNormalized = isNormalizedWith (const (const Nothing))

-- | ~Quickly~ Check if an expression is in normal form
isNormalizedWith :: forall m s a. StrMapIsh m => Eq s => Eq a => Normalizer a -> Expr m s a -> Boolean
isNormalizedWith ctx e0 = normalizeWith ctx e0 == e0

-- | Detect if the given variable is free within the given expression
freeIn :: forall m s a. Functor m => Eq1 m => Eq (m Unit) => Eq a => Var -> Expr m s a -> Boolean
freeIn variable expression =
    shift 1 variable strippedExpression /= strippedExpression
  where
    -- TODO: necessary?
    strippedExpression :: Expr m Void a
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

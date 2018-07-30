module Dhall.Core ( module Dhall.Core ) where

import Prelude

import Data.Array as Array
import Data.Const as ConstF
import Data.Foldable (all, any)
import Data.Function (on)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Mu (Mu(..))
import Data.Functor.Product (Product(..))
import Data.Functor.Variant (FProxy, SProxy(..), VariantF)
import Data.Functor.Variant as VariantF
import Data.HeytingAlgebra (tt, ff)
import Data.Identity (Identity(..))
import Data.Int (even, toNumber)
import Data.Lens as Lens
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..), fromMaybe, isNothing)
import Data.Maybe.First (First)
import Data.Newtype (class Newtype, under, unwrap, wrap)
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (Tuple(..), fst, snd)
import Dhall.Core.AST (AllTheThings, BuiltinBinOps, BuiltinFuncs, BuiltinOps, BuiltinTypes, BuiltinTypes2, Const(..), Expr(..), ExprRow, FunctorThings, LetF(..), Literals, Literals2, MergeF(..), OrdMap, Pair(..), SimpleThings, Syntax, Terminals, TextLitF(..), Triplet(..), Var(..), _Expr, _ExprF, coalesce1, unfurl) as Dhall.Core
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
    # VariantF.on (SProxy :: SProxy "Var")
      (unwrap >>> \(V x' n') ->
        let n'' = if x == x' && n <= n' then n' + d else n'
        in mkVar (V x' n'')
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
    # VariantF.on (SProxy :: SProxy "Var")
      (unwrap >>> \(V x' n') ->
        if x == x' && n == n' then e else mkVar (V x' n')
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
  go (Expr (In expr)) =
    ( ( map (go >>> unwrap)
    >>> VariantF.expand >>> In >>> Expr
      )
    # VariantF.on (SProxy :: SProxy "Lam")
      (\(Product (Tuple (Tuple x _A) (Identity b_0))) ->
        if x == "_" then mkLam x (go _A) (go b_0) else
        let
          b_1 = shift 1 (V "_" 0) b_0
          b_2 = subst (V x 0) (mkVar (V "_" 0)) b_1
          b_3 = shift (-1) (V x 0) b_2
          b_4 = alphaNormalize b_3
        in mkLam "_" (go _A) b_4
      )
    # VariantF.on (SProxy :: SProxy "Pi")
      (\(Product (Tuple (Tuple x _A) (Identity _B_0))) ->
        if x == "_" then mkPi x (go _A) (go _B_0) else
        let
          _B_1 = shift 1 (V "_" 0) _B_0
          _B_2 = subst (V x 0) (mkVar (V "_" 0)) _B_1
          _B_3 = shift (-1) (V x 0) _B_2
          _B_4 = alphaNormalize _B_3
        in mkPi "_" (go _A) _B_3
      )
    # VariantF.on (SProxy :: SProxy "Let")
      (\(LetF x mt a b_0) ->
        if x == "_" then mkLet x (map go mt) (go a) (go b_0) else
        let
          b_1 = shift 1 (V "_" 0) b_0
          b_2 = subst (V x 0) (mkVar (V "_" 0)) b_1
          b_3 = shift (-1) (V x 0) b_2
          b_4 = alphaNormalize b_3
        in mkLet "_" (go <$> mt) (go a) b_3
      )
    ) (Expr <$> expr)

-- | Reduce an expression to its normal form, performing beta reduction
-- | `normalize` does not type-check the expression.  You may want to type-check
-- | expressions before normalizing them since normalization can convert an
-- | ill-typed expression into a well-typed expression.
-- | However, `normalize` will not fail if the expression is ill-typed and will
-- | leave ill-typed sub-expressions unevaluated.
normalize :: forall s t a. Eq a => Expr s a -> Expr t a
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
type Normalizer a = forall s. Expr s a -> Expr s a -> Maybe (Expr s a)


modifyKey :: forall a k. Eq k =>
  k ->
  (Tuple k a -> Tuple k a) ->
  Array (Tuple k a) ->
  Maybe (Array (Tuple k a))
modifyKey k f as = do
  i <- Array.findIndex (fst >>> eq k) as
  Array.modifyAt i f as

deleteKey :: forall a k. Eq k =>
  k ->
  Array (Tuple k a) ->
  Maybe (Array (Tuple k a))
deleteKey k as = do
  i <- Array.findIndex (fst >>> eq k) as
  Array.deleteAt i as

unionWith :: forall k a. Ord k =>
  (a -> a -> a) ->
  Array (Tuple k a) -> Array (Tuple k a) ->
  Array (Tuple k a)
unionWith combine l' r' =
  let
    l = Array.nubBy (compare `on` fst) l'
    r = Array.nubBy (compare `on` fst) r'
    inserting as (Tuple k v) =
      case modifyKey k (map (combine <@> v)) as of
        Nothing -> as <> [Tuple k v]
        Just as' -> as'
  in Array.foldl inserting l r

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
normalizeWith :: forall s t a. Eq a => Normalizer a -> Expr s a -> Expr t a
normalizeWith ctx (Expr e0) = go e0 where
  onP :: forall e v r.
    Preview' e v ->
    (v -> r) -> (e -> r) ->
    e -> r
  onP p this other e = case Lens.preview p e of
    Just v -> this v
    _ -> other e

  previewE :: forall o o' e.
    Newtype o o' =>
    Preview' o' e ->
    o -> Maybe e
  previewE p = Lens.preview p <<< unwrap
  unPair :: forall o o' e r.
    Newtype o o' =>
    Preview' o' e ->
    (o -> o -> Maybe e -> Maybe e -> r) ->
    AST.Pair o ->
    r
  unPair p f (AST.Pair l r) = f l r (previewE p l) (previewE p r)
  unPairN :: forall o o' e e' r.
    Newtype o o' =>
    Newtype e e' =>
    Preview' o' e ->
    (o -> o -> Maybe e' -> Maybe e' -> r) ->
    AST.Pair o ->
    r
  unPairN p = unPair (unsafeCoerce p)

  mapExpr :: forall f st. f (Mu (VariantF (AST.ExprRow st a))) -> f (Expr st a)
  mapExpr = unsafeCoerce

  mapMapExpr :: forall f g st. f (g (Mu (VariantF (AST.ExprRow st a)))) -> f (g (Expr st a))
  mapMapExpr = unsafeCoerce

  -- The companion to judgmentallyEqual for terms that are already
  -- normalized recursively from this
  judgEq = eq `on` (alphaNormalize >>> unsafeCoerce :: Expr t a -> Expr Void a)

  go :: Mu (VariantF (AST.ExprRow s a)) -> Expr t a
  go (In e) =
    ( (VariantF.expand >>> In >>> Expr)
    # onP AST._BoolAnd
      (unPairN AST._BoolLit \l r -> case _, _ of
        Just true, _ -> Expr r -- (l = True) && r -> r
        Just false, _ -> Expr l -- (l = False) && r -> (l = False)
        _, Just false -> Expr r -- l && (r = False) -> (r = False)
        _, Just true -> Expr l -- l && (r = True) -> l
        _, _ ->
          if judgEq (Expr l) (Expr r)
          then Expr l
          else AST.mkBoolAnd (Expr l) (Expr r)
      )
    # onP AST._BoolOr
      (unPairN AST._BoolLit \l r -> case _, _ of
        Just true, _ -> Expr l -- (l = True) || r -> (l = True)
        Just false, _ -> Expr r -- (l = False) || r -> r
        _, Just false -> Expr l -- l || (r = False) -> l
        _, Just true -> Expr r -- l || (r = True) -> (r = True)
        _, _ ->
          if judgEq (Expr l) (Expr r)
          then Expr l
          else AST.mkBoolOr (Expr l) (Expr r)
      )
    # onP AST._BoolEQ
      (unPairN AST._BoolLit \l r -> case _, _ of
        Just a, Just b -> AST.mkBoolLit (a == b)
        _, _ ->
          if judgEq (Expr l) (Expr r)
          then AST.mkBoolLit true
          else AST.mkBoolEQ (Expr l) (Expr r)
      )
    # onP AST._BoolNE
      (unPairN AST._BoolLit \l r -> case _, _ of
        Just a, Just b -> AST.mkBoolLit (a /= b)
        _, _ ->
          if judgEq (Expr l) (Expr r)
          then AST.mkBoolLit false
          else AST.mkBoolNE (Expr l) (Expr r)
      )
    # onP AST._BoolIf
      (\(AST.Triplet b t f) ->
        let p = AST._BoolLit <<< _Newtype in
        case previewE p b of
          Just true -> Expr t
          Just false -> Expr f
          Nothing ->
            case previewE p t, previewE p f of
              Just true, Just false -> Expr b
              _, _ ->
                if judgEq (Expr t) (Expr f)
                  then Expr t
                  else AST.mkBoolIf (Expr b) (Expr t) (Expr f)
      )
    # onP AST._NaturalPlus
      (unPairN AST._NaturalLit \l r -> case _, _ of
        Just a, Just b -> AST.mkNaturalLit (a + b)
        Just 0, _ -> Expr r
        _, Just 0 -> Expr l
        _, _ -> AST.mkNaturalPlus (Expr l) (Expr r)
      )
    # onP AST._NaturalTimes
      (unPairN AST._NaturalLit \l r -> case _, _ of
        Just a, Just b -> AST.mkNaturalLit (a * b)
        Just 0, _ -> Expr l
        _, Just 0 -> Expr r
        Just 1, _ -> Expr r
        _, Just 1 -> Expr l
        _, _ -> AST.mkNaturalTimes (Expr l) (Expr r)
      )
    # onP AST._ListAppend
      (unPair AST._ListLit \l r -> case _, _ of
        Just { ty, values: a }, Just { values: b } ->
          AST.mkListLit (mapExpr ty) (mapExpr $ a <> b)
        Just { values: [] }, _ -> Expr r
        _, Just { values: [] } -> Expr l
        _, _ -> AST.mkListAppend (Expr l) (Expr r)
      )
    # onP AST._Combine
      (let
        decide = unPairN AST._RecordLit \l r -> case _, _ of
          Just a, Just b -> AST.mkRecordLit $ unsafeCoerce $
            unionWith (\x y -> unwrap $ decide (AST.Pair x y)) a b
          Just [], _ -> Expr r
          _, Just [] -> Expr l
          _, _ -> AST.mkCombine (Expr l) (Expr r)
      in decide)
    # onP AST._CombineTypes
      (let
        decide = unPairN AST._Record \l r -> case _, _ of
          Just a, Just b -> AST.mkRecord $ unsafeCoerce $
            unionWith (\x y -> unwrap $ decide (AST.Pair x y)) a b
          Just [], _ -> Expr r
          _, Just [] -> Expr l
          _, _ -> AST.mkCombineTypes (Expr l) (Expr r)
      in decide)
    # onP AST._Prefer
      (let
        decide = unPairN AST._RecordLit \l r -> case _, _ of
          Just a, Just b -> AST.mkRecordLit $ unsafeCoerce $
            unionWith const a b
          Just [], _ -> Expr r
          _, Just [] -> Expr l
          _, _ -> AST.mkPrefer (Expr l) (Expr r)
      in decide)
    # onP AST._Constructors
      (\e' -> case previewE AST._Union e' of
        Just (Compose kts) -> AST.mkRecord $ kts <#> \(Tuple k t_) -> Tuple k $
          AST.mkLam k (Expr t_) $ AST.mkUnionLit k (AST.mkVar (AST.V k 0)) $
            mapMapExpr $ (fromMaybe <*> deleteKey k) kts
        Nothing -> AST.mkConstructors (Expr e')
      )
    # onP AST._Let
      (\{ var, ty, value, body } ->
        let v = AST.V var 0 in normalizeWith ctx $
        shift (-1) v (subst v (shift 1 v (Expr value)) (Expr body))
      )
    # VariantF.on (SProxy :: SProxy "Note") (snd >>> Expr)
    # onP AST._App \{ fn, arg } ->
      onP AST._Lam
        (\{ var: x, body } ->
          let
            v = AST.V x 0
          in normalizeWith ctx $ shift (-1) v $
            subst v (shift 1 v (Expr arg)) (Expr body)
        ) <@> unwrap fn $ \_ ->
      case Lens.view apps (Expr fn), Lens.view apps (Expr arg) of
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
              zero = AST.mkNaturalLit 0
              succ = AST.mkLam "x" AST.mkNatural $
                AST.mkNaturalPlus (AST.mkVar (AST.V "x" 0)) $ AST.mkNaturalLit 1
              g' = Lens.review apps g
            in normalizeWith ctx $
              AST.mkApp (AST.mkApp (AST.mkApp g' AST.mkNatural) succ) zero
        naturaliszero, naturallit
          | noapp AST._NaturalIsZero naturaliszero
          , Just n <- noapplit AST._NaturalLit naturallit ->
            AST.mkBoolLit (n == 0)
        naturaleven, naturallit
          | noapp AST._NaturalEven naturaleven
          , Just n <- noapplit AST._NaturalLit naturallit ->
            AST.mkBoolLit (even n)
        naturalodd, naturallit
          | noapp AST._NaturalOdd naturalodd
          , Just n <- noapplit AST._NaturalLit naturallit ->
            AST.mkBoolLit (even n)
        naturaltointeger, naturallit
          | noapp AST._NaturalToInteger naturaltointeger
          , Just n <- noapplit AST._NaturalLit naturallit ->
            AST.mkIntegerLit n
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
          AST.mkApp (Expr fn) (Expr arg)
    ) (map (go >>> unwrap) e)

-- Little ADT to make destructuring applications easier for normalization
data Apps s a = App (Apps s a) (Apps s a) | NoApp (Expr s a)

noapplit :: forall s a v.
  Lens.Prism'
    (VariantF (AST.ExprRow s a) (Expr s a))
    (ConstF.Const v (Expr s a)) ->
  Apps s a ->
  Maybe v
noapplit p = Lens.preview (_NoApp <<< AST._E p <<< _Newtype)

noapp :: forall f s a. Functor f =>
  Lens.Prism'
    (VariantF (AST.ExprRow s a) (Expr s a))
    (f (Expr s a)) ->
  Apps s a ->
  Boolean
noapp p = Lens.is (_NoApp <<< AST._E p)

_NoApp :: forall s a. Lens.Prism' (Apps s a) (Expr s a)
_NoApp = Lens.prism' NoApp case _ of
  NoApp e -> Just e
  _ -> Nothing

apps :: forall s a. Lens.Iso' (Expr s a) (Apps s a)
apps = Lens.iso fromExpr toExpr where
  toExpr = case _ of
    App f a -> AST.mkApp (toExpr f) (toExpr a)
    NoApp e -> e
  fromExpr e =
    case Lens.preview (AST._E (AST._ExprFPrism (SProxy :: SProxy "App"))) e of
      Nothing -> NoApp e
      Just (AST.Pair fn arg) -> App (fromExpr fn) (fromExpr arg)

-- | Returns `true` if two expressions are α-equivalent and β-equivalent and
-- | `false` otherwise
judgmentallyEqual :: forall s t a. Eq a => Expr s a -> Expr t a -> Boolean
judgmentallyEqual eL0 eR0 = alphaBetaNormalize eL0 == alphaBetaNormalize eR0
  where
    alphaBetaNormalize :: forall st. Eq a => Expr st a -> Expr Void a
    alphaBetaNormalize = alphaNormalize <<< normalize

-- | Check if an expression is in a normal form given a context of evaluation.
-- | Unlike `isNormalized`, this will fully normalize and traverse through the expression.
--
-- | It is much more efficient to use `isNormalized`.
isNormalized :: forall s a. Eq s => Eq a => Expr s a -> Boolean
isNormalized = isNormalizedWith (const (const Nothing))

type Preview' a b = Lens.Fold (First b) a a b b

-- | Quickly check if an expression is in normal form
isNormalizedWith :: forall s a. Eq s => Eq a => Normalizer a -> Expr s a -> Boolean
isNormalizedWith ctx (Expr e0) = go e0 where
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

  samesies (AST.Pair a b) = alphaNormalize (Expr a) == alphaNormalize (Expr b)

  go :: Mu (VariantF (AST.ExprRow s a)) -> Boolean
  go (In e) = if not all go e then false else
    ( tt
    # onP AST._BoolAnd
      (all (ain't AST._BoolLit) && not samesies)
    # onP AST._BoolOr
      (all (ain't AST._BoolLit) && not samesies)
    # onP AST._BoolEQ
      (any (ain't AST._BoolLit) && not samesies)
    # onP AST._BoolNE
      (any (ain't AST._BoolLit) && not samesies)
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
    # VariantF.on (SProxy :: SProxy "Note") ff
    # onP AST._App \{ fn, arg } ->
      ( (\_ _ -> isNothing (ctx (Expr fn) (Expr arg)))
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
    -- TODO: necessary?
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

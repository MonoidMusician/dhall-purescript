module Dhall.Normalize where

import Prelude

import Data.Const as ConstF
import Data.Function (on)
import Data.Functor.Variant (VariantF)
import Data.Functor.Variant as VariantF
import Data.FunctorWithIndex (mapWithIndex)
import Data.Int (even, toNumber)
import Data.Lens as Lens
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Maybe.First (First)
import Data.Natural (natToInt)
import Data.Newtype (class Newtype, unwrap)
import Data.These (These(..))
import Dhall.Core.AST (Expr, projectW)
import Dhall.Core.AST as AST
import Dhall.Core.AST.Types.Basics (S_, _S)
import Dhall.Core.StrMapIsh (class StrMapIsh)
import Dhall.Core.StrMapIsh as StrMapIsh
import Dhall.Variables as Variables
import Matryoshka (class Recursive, project)
import Unsafe.Coerce (unsafeCoerce)

-- | Reduce an expression to its normal form, performing beta reduction
-- | `normalize` does not type-check the expression.  You may want to type-check
-- | expressions before normalizing them since normalization can convert an
-- | ill-typed expression into a well-typed expression.
-- | However, `normalize` will not fail if the expression is ill-typed and will
-- | leave ill-typed sub-expressions unevaluated.
normalize :: forall m a. StrMapIsh m => Eq a => Expr m a -> Expr m a
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
boundedType :: forall m a. Expr m a -> Boolean
boundedType _ = false

-- | Use this to wrap you embedded functions (see `normalizeWith`) to make them
-- | polymorphic enough to be used.
type Normalizer m a = Expr m a -> Expr m a -> Maybe (Expr m a)

newtype WrappedNormalizer m a = WrappedNormalizer (Normalizer m a)
-- not Alt, because it is not a covariant functor
instance semigroupWrappedNormalizer :: Semigroup (WrappedNormalizer m a) where
  append (WrappedNormalizer n) (WrappedNormalizer m) = WrappedNormalizer \fn arg ->
    case n fn arg of
      Just r -> Just r
      Nothing -> m fn arg
instance monoidWrappedNormalizer :: Monoid (WrappedNormalizer m a) where
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
normalizeWith :: forall m a. StrMapIsh m => Eq a => Normalizer m a -> Expr m a -> Expr m a
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
  judgEq = eq `on` Variables.alphaNormalize

  rules = identity
    >>> VariantF.on (_S::S_ "Annot")
      (\(AST.Pair e _) -> e)
    >>> VariantF.on (_S::S_ "BoolAnd")
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
    >>> VariantF.on (_S::S_ "BoolOr")
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
    >>> VariantF.on (_S::S_ "BoolEQ")
      (unPairN AST._BoolLit \l r -> case _, _ of
        Just a, Just b -> AST.mkBoolLit (a == b)
        _, _ ->
          if judgEq (l) (r)
          then AST.mkBoolLit true
          else AST.mkBoolEQ (l) (r)
      )
    >>> VariantF.on (_S::S_ "BoolNE")
      (unPairN AST._BoolLit \l r -> case _, _ of
        Just a, Just b -> AST.mkBoolLit (a /= b)
        _, _ ->
          if judgEq (l) (r)
          then AST.mkBoolLit false
          else AST.mkBoolNE (l) (r)
      )
    >>> VariantF.on (_S::S_ "BoolIf")
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
    >>> VariantF.on (_S::S_ "NaturalPlus")
      (unPairN AST._NaturalLit \l r -> case _, _ of
        Just a, Just b -> AST.mkNaturalLit (a + b)
        Just a, _ | a == zero -> r
        _, Just b | b == zero -> l
        _, _ -> AST.mkNaturalPlus (l) (r)
      )
    >>> VariantF.on (_S::S_ "NaturalTimes")
      (unPairN AST._NaturalLit \l r -> case _, _ of
        Just a, Just b -> AST.mkNaturalLit (a * b)
        Just a, _ | a == zero -> l
        _, Just b | b == zero -> r
        Just a, _ | a == one -> r
        _, Just b | b == one -> l
        _, _ -> AST.mkNaturalTimes (l) (r)
      )
    >>> VariantF.on (_S::S_ "ListAppend")
      (unPair AST._ListLit \l r -> case _, _ of
        Just { ty, values: a }, Just { values: b } ->
          AST.mkListLit ty (a <> b)
        Just { values: [] }, _ -> r
        _, Just { values: [] } -> l
        _, _ -> AST.mkListAppend (l) (r)
      )
    >>> VariantF.on (_S::S_ "Combine")
      (let
        decideThese = Just <<< case _ of
          This a -> a
          That b -> b
          Both a b -> decide (AST.Pair a b)
        decide = unPair AST._RecordLit \l r -> case _, _ of
          Just a, Just b -> AST.mkRecordLit $
            StrMapIsh.unionWith (pure decideThese) a b
          Just a, _ | StrMapIsh.isEmpty a -> r
          _, Just b | StrMapIsh.isEmpty b -> l
          _, _ -> AST.mkCombine (l) (r)
      in decide)
    >>> VariantF.on (_S::S_ "CombineTypes")
      (let
        decideThese = Just <<< case _ of
          This a -> a
          That b -> b
          Both a b -> decide (AST.Pair a b)
        decide = unPair AST._Record \l r -> case _, _ of
          Just a, Just b -> AST.mkRecord $
            StrMapIsh.unionWith (pure decideThese) a b
          Just a, _ | StrMapIsh.isEmpty a -> r
          _, Just b | StrMapIsh.isEmpty b -> l
          _, _ -> AST.mkCombineTypes (l) (r)
      in decide)
    >>> VariantF.on (_S::S_ "Prefer")
      (let
        preference = Just <<< case _ of
          This a -> a
          That b -> b
          Both a _ -> a
        decide = unPair AST._RecordLit \l r -> case _, _ of
          Just a, Just b -> AST.mkRecordLit $
            StrMapIsh.unionWith (pure preference) a b
          Just a, _ | StrMapIsh.isEmpty a -> r
          _, Just b | StrMapIsh.isEmpty b -> l
          _, _ -> AST.mkPrefer (l) (r)
      in decide)
    >>> VariantF.on (_S::S_ "Constructors")
      (unwrap >>> \e' -> case previewE AST._Union e' of
        Just kts -> AST.mkRecord $ kts # mapWithIndex \k t_ ->
          AST.mkLam k (t_) $ AST.mkUnionLit k (AST.mkVar (AST.V k 0)) $
            (fromMaybe <*> StrMapIsh.delete k) kts
        Nothing -> AST.mkConstructors (e')
      )
    >>> onP AST._Let
      (\{ var, ty, value, body } ->
        normalizeWith ctx $ Variables.shiftSubstShift0 var value body
      )
    -- NOTE: eta-normalization, added
    >>> onP AST._Lam
      (\{ var, ty, body } ->
        AST.projectW body #
        let
          default :: forall x. x -> Expr m a
          default _ = AST.embedW (Lens.review AST._Lam { var, ty, body })
        in default # onP AST._App
          \{ fn, arg } ->
            let var0 = AST.V var 0 in
            if judgEq arg (AST.mkVar var0) && not Variables.freeIn var0 fn
              then fn
              else default unit
      )
    -- composing with <<< gives this case priority
    >>> identity <<< onP AST._App \{ fn, arg } ->
      onP AST._Lam
        (\{ var, body } ->
          normalizeWith ctx $ Variables.shiftSubstShift0 var arg body
        ) <@> projectW fn $ \_ ->
      case Lens.view apps fn, Lens.view apps arg of
        -- build/fold fusion for `List`
        -- App (App ListBuild _) (App (App ListFold _) e') -> loop e'
        listbuild~_, listfold~_~e'
          | noapp AST._ListBuild listbuild
          , noapp AST._ListFold listfold ->
            Lens.review apps e'
        -- build/fold fusion for `Natural`
        -- App NaturalBuild (App NaturalFold e') -> loop e'
        naturalbuild, naturalfold~e'
          | noapp AST._NaturalBuild naturalbuild
          , noapp AST._NaturalFold naturalfold ->
            Lens.review apps e'
        -- build/fold fusion for `Optional`
        -- App (App OptionalBuild _) (App (App OptionalFold _) e') -> loop e'
        optionalbuild~_, optionalfold~_~e'
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
        _, _ | Just ret <- ctx fn arg -> ret
        _, _ ->
          AST.mkApp fn arg

-- Little ADT to make destructuring applications easier for normalization
data Apps m a = App (Apps m a) (Apps m a) | NoApp (Expr m a)
infixl 0 App as ~

noapplit :: forall m a v.
  Lens.Prism'
    (VariantF (AST.ExprLayerRow m a) (Expr m a))
    (ConstF.Const v (Expr m a)) ->
  Apps m a ->
  Maybe v
noapplit p = Lens.preview (_NoApp <<< AST._E p <<< _Newtype)

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

-- | Returns `true` if two expressions are α-equivalent and β-equivalent and
-- | `false` otherwise
judgmentallyEqual :: forall m a. StrMapIsh m => Eq a => Expr m a -> Expr m a -> Boolean
judgmentallyEqual eL0 eR0 = alphaBetaNormalize eL0 == alphaBetaNormalize eR0
  where
    alphaBetaNormalize :: Expr m a -> Expr m a
    alphaBetaNormalize = Variables.alphaNormalize <<< normalize

-- | Check if an expression is in a normal form given a context of evaluation.
-- | Unlike `isNormalized`, this will fully normalize and traverse through the expression.
--
-- | It is much more efficient to use `isNormalized`.
isNormalized :: forall m a. StrMapIsh m => Eq a => Expr m a -> Boolean
isNormalized = isNormalizedWith (const (const Nothing))

-- | ~Quickly~ Check if an expression is in normal form
isNormalizedWith :: forall m a. StrMapIsh m => Eq a => Normalizer m a -> Expr m a -> Boolean
isNormalizedWith ctx e0 = normalizeWith ctx e0 == e0

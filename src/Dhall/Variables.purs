module Dhall.Variables where

import Prelude

import Control.Comonad.Env (mapEnvT)
import Data.Const (Const(..))
import Data.Eq (class Eq1)
import Data.Functor.Variant (class VariantFMapCases, class VariantFMaps, VariantF)
import Data.Functor.Variant as VariantF
import Data.HeytingAlgebra (ff)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Newtype (over, unwrap)
import Data.Variant (Variant)
import Data.Variant as Variant
import Data.Variant.Internal (class VariantTags)
import Dhall.Core.AST (BindingBody(..), Expr, LetF(..), S_, Var(..), Variable, CONST, _S, mkLam, mkLet, mkPi, mkVar)
import Dhall.Core.AST as AST
import Dhall.Core.AST.Noted as Noted
import Dhall.Core.Zippers.Recursive (_recurse)
import Type.Row (type (+))
import Type.Row as R

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
shift d v = AST.rewriteTopDown (shiftAlg d v)

-- TODO: factor out explicit recursion, generalize to Expr-like things
type VariableAlg m a = forall r.
  (VariantF r (Expr m a) -> Expr m a) ->
  VariantF (Variable m + r) (Expr m a) ->
  Expr m a

newtype SimpleMapCasesOn affected node = SimpleMapCasesOn
  forall cases casesrl.
    R.RowToList cases casesrl =>
    VariantFMapCases casesrl affected affected node node =>
  Record cases -> node -> node

run :: forall cases casesrl affected node.
    R.RowToList cases casesrl =>
    VariantFMapCases casesrl affected affected node node =>
  SimpleMapCasesOn affected node ->
  Record cases -> node -> node
run (SimpleMapCasesOn f) = f

type GenericExprAlgebra (affected :: (Type -> Type) -> # Type -> # Type) i node = forall r m.
  i ->
  { layer :: VariantF (affected m + r) node -> node
  , unlayer :: node -> VariantF (affected m + r) node
  , overlayer :: SimpleMapCasesOn (affected m + ()) node
  , recurse :: i -> node -> node
  } ->
  node -> node

type GenericExprAlgebraV (affected :: (Type -> Type) -> # Type -> # Type) (i :: Type -> # Type -> # Type) = forall node.
  GenericExprAlgebra affected (Variant (i node ())) node

type GenericExprAlgebraVT (affected :: (Type -> Type) -> # Type -> # Type) (i :: Type -> # Type -> # Type) = forall node v v' r m.
    -- R.Union v (i node ()) (i node v) =>
  (Variant v -> GenericExprAlgebrarm' affected (Variant (i node v')) node r m) ->
  (Variant (i node v) -> GenericExprAlgebrarm' affected (Variant (i node v')) node r m)

type GenericExprAlgebra' (affected :: (Type -> Type) -> # Type -> # Type) i node = forall r m.
  { layer :: VariantF (affected m + r) node -> node
  , unlayer :: node -> VariantF (affected m + r) node
  , overlayer :: SimpleMapCasesOn (affected m + ()) node
  , recurse :: i -> node -> node
  } ->
  node -> node

type GenericExprAlgebrarm' (affected :: (Type -> Type) -> # Type -> # Type) i node r m =
  { layer :: VariantF (affected m + r) node -> node
  , unlayer :: node -> VariantF (affected m + r) node
  , overlayer :: SimpleMapCasesOn (affected m + ()) node
  , recurse :: i -> node -> node
  } ->
  node -> node

overlayerExpr ::
  forall m a cases casesrl r rl untouched.
    R.RowToList cases casesrl =>
    VariantFMapCases casesrl r r (Expr m a) (Expr m a) =>
    R.RowToList r rl =>
    VariantTags rl =>
    VariantFMaps rl =>
    R.Union r untouched (AST.ExprLayerRow m a) =>
  Record cases -> Expr m a -> Expr m a
overlayerExpr cases = _recurse <<< _Newtype $
  VariantF.mapSomeExpand cases identity

overlayerNoted ::
  forall m s a cases casesrl r rl untouched.
    R.RowToList cases casesrl =>
    VariantFMapCases casesrl r r (Noted.Expr m s a) (Noted.Expr m s a) =>
    R.RowToList r rl =>
    VariantTags rl =>
    VariantFMaps rl =>
    R.Union r untouched (AST.ExprLayerRow m a) =>
  Record cases -> Noted.Expr m s a -> Noted.Expr m s a
overlayerNoted cases = _recurse $ mapEnvT $ over AST.ERVF $
  VariantF.mapSomeExpand cases identity

shiftAlg :: forall m a. Int -> Var -> VariableAlg m a
shiftAlg d v@(V x n) = identity
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

type ShiftAlg node v = ( shift :: { delta :: Int, variable :: Var } | v )
shiftAlgG :: GenericExprAlgebraVT Variable ShiftAlg
shiftAlgG rest = rest # Variant.on (_S::S_ "shift")
  \{ delta, variable: V x n } node -> run node.overlayer
    let recur = node.recurse <<< Variant.inj (_S::S_ "shift") <<< { delta, variable: _ } in
    { "Var": over Const \(V x' n') ->
      let n'' = if x == x' && n <= n' then n' + delta else n'
      in V x' n''
    , "Lam": \(BindingBody x' _A b) ->
        let
          _A' = recur (V x n ) _A
          b'  = recur (V x n') b
          n' = if x == x' then n + 1 else n
        in BindingBody x' _A' b'
    , "Pi": \(BindingBody x' _A _B) ->
        let
          _A' = recur (V x n ) _A
          _B'  = recur (V x n') _B
          n' = if x == x' then n + 1 else n
        in BindingBody x' _A' _B'
    , "Let": \(LetF f mt r b) ->
        let
          n' = if x == f then n + 1 else n
          b' =  recur (V x n') b
          mt' = recur (V x n ) <$> mt
          r'  = recur (V x n ) r
        in LetF f mt' r' b'
    }

-- | Substitute all occurrences of a variable with an expression
-- | `subst x C B  ~  B[x := C]`
subst :: forall m a. Var -> Expr m a -> Expr m a -> Expr m a
subst v e = AST.rewriteTopDown (substAlg v e)

substAlg :: forall m a. Var -> Expr m a -> VariableAlg m a
substAlg v@(V x n) e = identity
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

type SubstAlg node v = ( subst :: { variable :: Var, substitution :: node } | v )
type ShiftSubstAlg node v = ShiftAlg node + SubstAlg node + v
shiftSubstAlgG :: GenericExprAlgebraVT Variable ShiftSubstAlg
shiftSubstAlgG rest = rest # shiftAlgG <<< Variant.on (_S::S_ "subst") \{ variable: variable@(V x n), substitution } node -> run node.overlayer
  let
    substIfTarget c = node.unlayer >>> VariantF.on (_S::S_ "Var")
      (eq (Const variable)) ff >>=
      if _ then pure substitution else c
    subst1 v' s' = node.recurse <<< Variant.inj (_S::S_ "subst") $ { variable: v', substitution: s' }
    shift1 = node.recurse <<< Variant.inj (_S::S_ "shift") <<< { delta: 1, variable: _ }
  in
  { "Var": identity identity
  , "Lam": \(BindingBody x' _A b) ->
      let
        _A' = subst1 (V x n )                  substitution  _A
        b'  = subst1 (V x n') (shift1 (V x' 0) substitution) b
        n'  = if x == x' then n + 1 else n
      in BindingBody x' _A' b'
  , "Pi": \(BindingBody x' _A _B) ->
      let
        _A' = subst1 (V x n )                  substitution  _A
        _B' = subst1 (V x n') (shift1 (V x' 0) substitution) _B
        n'  = if x == x' then n + 1 else n
      in BindingBody x' _A' _B'
  , "Let": \(LetF f mt r b) ->
      let
        n' = if x == f then n + 1 else n
        b'  = subst1 (V x n') (shift1 (V f 0) substitution) b
        mt' = subst1 (V x n) substitution <$> mt
        r'  = subst1 (V x n) substitution r
      in LetF f mt' r' b'
  }

-- | The usual combination of subst and shift required for proper substitution.
shiftSubstShift :: forall m a. Var -> Expr m a -> Expr m a -> Expr m a
shiftSubstShift v a b = shift (-1) v (subst v (shift 1 v a) b)

shiftSubstShift0 :: forall m a. String ->  Expr m a -> Expr m a -> Expr m a
shiftSubstShift0 v = shiftSubstShift $ AST.V v 0

rename :: forall m a. Var -> Var -> Expr m a -> Expr m a
rename v0 v1 = shift (-1) v0 <<< subst v0 (mkVar v1) <<< shift 1 v1

-- TODO: is this fusion okay? is this even fusion? could it be more fused?
doRenameAlgG :: forall node ops v r. Var -> Var ->
  { layer :: VariantF ( "Var" :: CONST Var | r ) node -> node
  , recurse :: Variant (ShiftSubstAlg node v) -> node -> node
  | ops
  } ->
  node -> node
doRenameAlgG v0 v1 _ | v0 == v1 = identity
doRenameAlgG v0 v1 node = identity
  >>> node.recurse (Variant.inj (_S::S_ "shift") { delta: 1, variable: v1 })
  >>> node.recurse (Variant.inj (_S::S_ "subst") { variable: v0, substitution: newV })
  >>> node.recurse (Variant.inj (_S::S_ "shift") { delta: -1, variable: v0 })
  where
    newV = node.layer $ VariantF.inj (_S::S_ "Var") (Const v1)

-- | α-normalize an expression by renaming all variables to `"_"` and using
-- | De Bruijn indices to distinguish them
alphaNormalize :: forall m a. Expr m a -> Expr m a
alphaNormalize e = AST.rewriteTopDown alphaNormalizeAlg e

alphaNormalizeAlg :: forall m a. VariableAlg m a
alphaNormalizeAlg = identity
  >>> VariantF.on (_S::S_ "Var") (unwrap >>> mkVar)
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

type AlphaNormalizeAlg node v = ShiftSubstAlg node + ( "alphaNormalize" :: Unit | v )
alphaNormalizeAlgG :: GenericExprAlgebraVT Variable AlphaNormalizeAlg
alphaNormalizeAlgG rest = rest # shiftSubstAlgG <<< Variant.on (_S::S_ "alphaNormalize") \_ node -> run node.overlayer
  let
    norm = node.recurse <<< Variant.inj (_S::S_ "alphaNormalize") $ unit
    renam v0 v1 = norm <<< doRenameAlgG v0 v1 node
  in
  { "Var": identity identity
  , "Lam": \(BindingBody x _A b) ->
      BindingBody "_" (norm _A) (renam (V x 0) (V "_" 0) b)
  , "Pi": \(BindingBody x _A _B) ->
      BindingBody "_" (norm _A) (renam (V x 0) (V "_" 0) _B)
  , "Let": \(LetF x mt a b) ->
      LetF "_" (norm <$> mt) (norm a) (renam (V x 0) (V "_" 0) b)
  }

-- | Detect if the given variable is free within the given expression
freeIn :: forall m a. Functor m => Eq1 m => Eq a => Var -> Expr m a -> Boolean
freeIn variable expression =
    shift 1 variable expression /= expression

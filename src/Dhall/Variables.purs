module Dhall.Variables where

import Prelude

import Control.Comonad (extract)
import Control.Comonad.Env (mapEnvT)
import Data.Const (Const(..))
import Data.Foldable (class Foldable, fold)
import Data.Functor.Variant (class VariantFMapCases, class VariantFMaps, SProxy, VariantF)
import Data.Functor.Variant as VariantF
import Data.HeytingAlgebra (ff)
import Data.Monoid.Disj (Disj(..))
import Data.Newtype (over, unwrap, wrap)
import Data.Symbol (class IsSymbol)
import Data.Tuple (Tuple(..))
import Data.Variant (Variant)
import Data.Variant as Variant
import Data.Variant.Internal (class VariantTags)
import Dhall.Core.AST (BindingBody(..), CONST, Expr, LetF(..), S_, Var(..), Variable, _S, mkVar)
import Dhall.Core.AST as AST
import Dhall.Core.AST.Noted as Noted
import Dhall.Core.Zippers.Recursive (_recurse)
import Matryoshka (Algebra, cata, embed, project)
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
shift d v = runAlgebraExpr (Variant.case_ # shiftAlgG) $
  Variant.inj (_S::S_ "shift") { delta: d, variable: v }

newtype SimpleMapCasesOn affected node = SimpleMapCasesOn
  (((VariantF affected node -> VariantF affected node) -> (node -> node)))

run :: forall cases casesrl affected affectedrl unaffected all node.
    R.RowToList cases casesrl =>
    VariantFMapCases casesrl affected affected node node =>
    R.RowToList affected affectedrl =>
    VariantTags affectedrl =>
    VariantFMaps affectedrl =>
    R.Union affected unaffected all =>
  SimpleMapCasesOn all node ->
  (node -> node) ->
  Record cases -> node -> node
run (SimpleMapCasesOn f) rest cases = f (VariantF.mapSomeExpand cases rest)

type NodeOps all i node ops =
  ( unlayer :: node -> VariantF all node
  , overlayer :: SimpleMapCasesOn all node
  , recurse :: i -> node -> node
  | ops
  )
type ConsNodeOps all i node ops = NodeOps all i node +
  ( layer :: VariantF all node -> node | ops )

type GenericExprAlgebra' ops i node =
  Record ops -> node -> node

type GenericExprAlgebra ops i node =
  i -> GenericExprAlgebra' ops i node

type GenericExprAlgebraVT (ops :: # Type -> Type -> Type -> # Type -> # Type) affected (i :: Type -> # Type -> # Type) =
  forall node v v' r ops'.
    -- R.Union v (i node ()) (i node v) =>
  (Variant v -> Record (ops (affected + r) (Variant (i node v')) node + ops') -> node -> node) ->
  (Variant (i node v) -> Record (ops (affected + r) (Variant (i node v')) node + ops') -> node -> node)

runAlgebraExpr :: forall i m a.
  GenericExprAlgebra (ConsNodeOps (AST.ExprLayerRow m a) i (Expr m a) ()) i (Expr m a) ->
  i -> Expr m a -> Expr m a
runAlgebraExpr alg = go where
  go i = alg i
    { unlayer: project >>> unwrap
    , layer: embed <<< wrap
    , overlayer: SimpleMapCasesOn (_recurse <<< over AST.ERVF)
    , recurse: go
    }

runAlgebraNoted :: forall i m a s.
  s ->
  GenericExprAlgebra (ConsNodeOps (AST.ExprLayerRow m a) i (Noted.Expr m s a) ()) i (Noted.Expr m s a) ->
  i -> Noted.Expr m s a -> Noted.Expr m s a
runAlgebraNoted df alg = go where
  go i = alg i
    { unlayer: project >>> unwrap >>> extract >>> unwrap
    , layer: embed <<< wrap <<< Tuple df <<< wrap
    , overlayer: SimpleMapCasesOn (_recurse <<< mapEnvT <<< over AST.ERVF)
    , recurse: go
    }

elim1 ::
  forall sym i v v_ v' v'_ cases casesrl affected affectedrl unaffected all node ops.
    IsSymbol sym =>
    R.Cons sym i v_ v =>
    R.Cons sym i v'_ v' =>
    R.RowToList cases casesrl =>
    VariantFMapCases casesrl affected affected node node =>
    R.RowToList affected affectedrl =>
    VariantTags affectedrl =>
    VariantFMaps affectedrl =>
    R.Union affected unaffected all =>
  SProxy sym ->
  (i          ->
  { overlayer :: SimpleMapCasesOn all node
  , recurse :: Variant v' -> node -> node
  | ops
  } -> Record cases
  ) ->
  (Variant v_ ->
  { overlayer :: SimpleMapCasesOn all node
  , recurse :: Variant v' -> node -> node
  | ops
  } -> (node -> node)) ->
  (Variant v  ->
  { overlayer :: SimpleMapCasesOn all node
  , recurse :: Variant v' -> node -> node
  | ops
  } -> (node -> node))
elim1 sym handler = Variant.on sym \i node ->
  run node.overlayer
    (node.recurse $ Variant.inj sym i)
    (handler i node)

trackVarBindingBody :: forall a b.
  Var -> (Var -> a -> b) -> BindingBody a -> BindingBody b
trackVarBindingBody (V x n) next (BindingBody x' _A b) =
  let
    _A' = next (V x n ) _A
    b'  = next (V x n') b
    n' = if x == x' then n + 1 else n
  in BindingBody x' _A' b'

trackVarLetF :: forall a b.
  Var -> (Var -> a -> b) -> LetF a -> LetF b
trackVarLetF (V x n) next (LetF x' mt r b) =
  let
    n' = if x == x' then n + 1 else n
    b' =  next (V x n') b
    mt' = next (V x n ) <$> mt
    r'  = next (V x n ) r
  in LetF x' mt' r' b'

trackVar :: forall m v a b. Var -> (Var -> a -> b) ->
  VariantF (Variable m + v) a -> VariantF (Variable m + v) b
trackVar v@(V x n) next = VariantF.mapSomeExpand
  { "Var": over Const identity
  , "Lam": trackVarBindingBody v next
  , "Pi": trackVarBindingBody v next
  , "Let": trackVarLetF v next
  }
  (next v)

type ShiftAlg node v = ( shift :: { delta :: Int, variable :: Var } | v )
shiftAlgG :: forall m. GenericExprAlgebraVT NodeOps (Variable m) ShiftAlg
shiftAlgG = elim1 (_S::S_ "shift")
  \i@{ delta, variable: v@(V x n) } node ->
    let recur = node.recurse <<< Variant.inj (_S::S_ "shift") <<< { delta, variable: _ } in
    { "Var": over Const \(V x' n') ->
      let n'' = if x == x' && n <= n' then n' + delta else n'
      in V x' n''
    , "Lam": trackVarBindingBody v recur
    , "Pi": trackVarBindingBody v recur
    , "Let": trackVarLetF v recur
    }

freeInAlg ::
  forall m v rl.
    R.RowToList (Variable m + v) rl =>
    VariantF.FoldableVFRL rl (Variable m + v) =>
  Algebra (VariantF (Variable m + v)) (Var -> Disj Boolean)
freeInAlg layer v | layer # VariantF.on (_S::S_ "Var") (eq (Const v)) ff = Disj true
freeInAlg layer v = layer # trackVar v ((#)) >>> fold

-- | Substitute all occurrences of a variable with an expression
-- | `subst x C B  ~  B[x := C]`
subst :: forall m a. Var -> Expr m a -> Expr m a -> Expr m a
subst v e = runAlgebraExpr (Variant.case_ # shiftSubstAlgG) $
  Variant.inj (_S::S_ "subst") { variable: v, substitution: e }

type SubstAlg node v = ( subst :: { variable :: Var, substitution :: node } | v )
type ShiftSubstAlg node v = ShiftAlg node + SubstAlg node + v
shiftSubstAlgG :: forall m. GenericExprAlgebraVT NodeOps (Variable m) ShiftSubstAlg
shiftSubstAlgG rest = rest # shiftAlgG <<< elim1 (_S::S_ "subst")
  \i@{ variable: variable@(V x n), substitution } node ->
  let
    substIfTarget c = node.unlayer >>> VariantF.on (_S::S_ "Var")
      (eq (Const variable)) ff >>=
      if _ then pure substitution else c
    subst1 v' s' = node.recurse <<< Variant.inj (_S::S_ "subst") $ { variable: v', substitution: s' }
    shift1 = node.recurse <<< Variant.inj (_S::S_ "shift") <<< { delta: 1, variable: _ }
  in
  { "Var": identity identity
  , "Lam": trackVarBindingBody variable subst1 >>>
    \(BindingBody x' _A b) -> BindingBody x'
        do _A $                 substitution
        do b  $ shift1 (V x' 0) substitution
  , "Pi": trackVarBindingBody variable subst1 >>>
    \(BindingBody x' _A _B) -> BindingBody x'
        do _A $                 substitution
        do _B $ shift1 (V x' 0) substitution
  , "Let": trackVarLetF variable subst1 >>>
    \(LetF x' mt r b) -> LetF x'
        do mt <@> substitution
        do r   $  substitution
        do b   $  shift1 (V x' 0) substitution
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
alphaNormalize = runAlgebraExpr (Variant.case_ # alphaNormalizeAlgG) $
  Variant.inj (_S::S_ "alphaNormalize") {}

type AlphaNormalizeAlg node v = ShiftSubstAlg node + ( "alphaNormalize" :: {} | v )
alphaNormalizeAlgG :: forall m. GenericExprAlgebraVT ConsNodeOps (Variable m) AlphaNormalizeAlg
alphaNormalizeAlgG rest = rest # shiftSubstAlgG <<< elim1 (_S::S_ "alphaNormalize") \_ node ->
  let
    norm = node.recurse <<< Variant.inj (_S::S_ "alphaNormalize") $ {}
    renam "_" = norm
    renam x = norm <<< doRenameAlgG (V x 0) (V "_" 0) node
  in
  { "Var": identity identity
  , "Lam": \(BindingBody x _A b) ->
      BindingBody "_" (norm _A) (renam x b)
  , "Pi": \(BindingBody x _A _B) ->
      BindingBody "_" (norm _A) (renam x _B)
  , "Let": \(LetF x mt a b) ->
      LetF "_" (norm <$> mt) (norm a) (renam x b)
  }

-- | Detect if the given variable is free within the given expression
freeIn :: forall m a. Foldable m => Var -> Expr m a -> Disj Boolean
freeIn = flip $ cata \e v -> freeInAlg (unwrap e) v

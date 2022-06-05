module Dhall.Core.AST.Operations.Transformations where

import Prelude

import Control.Comonad (extract)
import Control.Comonad.Env (EnvT(..))
import Data.Functor.Variant (class VariantFMapCases, class VariantFMaps, VariantF)
import Data.Functor.Variant as VariantF
import Data.Identity (Identity(..))
import Data.Newtype (un, unwrap, wrap)
import Data.Newtype as N
import Data.Profunctor.Star (Star(..))
import Data.Symbol (class IsSymbol)
import Data.Traversable (class Traversable)
import Data.Tuple (Tuple(..))
import Data.Variant (Variant)
import Data.Variant as Variant
import Data.Variant.Internal (class VariantFTraverseCases, class VariantTags)
import Dhall.Core.AST (Expr)
import Dhall.Core.AST as AST
import Dhall.Core.AST.Noted as Noted
import Dhall.Core.Zippers.Recursive (_recurse)
import Matryoshka (embed, project)
import Type.Row as R
import Type.RowList as RL
import Type.Proxy (Proxy)

-- The general shape of a transformation that runs over an Expr-like object
-- (top-down, with explicit recursion).
--
-- `i` is input to the algorithm as well as its internal language; `Variant`
-- enables extensibility here.
--
-- `ops` represents the operations that inspect and manipulate the structure;
-- see `NodeOps` and `ConsNodeOps` for more.
type GenericExprAlgebra ops i node = GenericExprAlgebraM Identity ops i node
type GenericExprAlgebraM m ops i node =
  i -> Record ops -> node -> m node

-- This is the type of a transformation that handles a couple cases of a Variant
-- input.
type GenericExprAlgebraVT (ops :: Row (Type -> Type) -> Type -> Type -> Row Type -> Row Type) affected (i :: Type -> Row Type -> Row Type) =
  forall (node :: Type) (v :: Row Type) (v' :: Row Type) (r :: Row (Type -> Type)) ops'.
  (Variant v -> Record (ops (affected r) (Variant (i node v')) node ops') -> node -> Identity node) ->
  (Variant (i node v) -> Record (ops (affected r) (Variant (i node v')) node ops') -> node -> Identity node)

type GenericExprAlgebraVTM m (ops :: Row (Type -> Type) -> Type -> Type -> Row Type -> Row Type) affected (i :: Type -> Row Type -> Row Type) =
  forall (node :: Type) (v :: Row Type) (v' :: Row Type) (r :: Row (Type -> Type)) ops'. Traversable (VariantF r) =>
  (Variant v -> Record (ops (affected r) (Variant (i node v')) node ops') -> node -> m node) ->
  (Variant (i node v) -> Record (ops (affected r) (Variant (i node v')) node ops') -> node -> m node)

-- The operations on a node of type `node` which has cases given by `all`,
-- with input (internal language) `i`.
--
-- `unlayer` peeks at one layer of Expr-like structure, thus discarding
-- any excess structure.
--
-- `overlayer` maps over one layer of structure, mapping each case to itself
-- and keeping any excess structure in the process; see `OverCases` for more.
-- (That is, it cannot modify the type of a node, only its contents.
-- This provides a nice guarantee, such that pointers in the structure
-- will be held constant.)
--
-- `recurse` enables recursing the algorithm; must be called explicitly.
type NodeOps all i node ops = NodeOpsM Identity all i node ops
type NodeOpsM m all i node ops =
  ( unlayer :: node -> VariantF all node
  , overlayer :: OverCasesM m all node
  , recurse :: i -> node -> m node
  | ops
  )
-- Same as above, plus:
-- `layer` generates a new layer for the structure, which thus cannot
-- include nor preserve any extra structure beside the Expr cases.
-- Prefer `overlayer` when possible.
type ConsNodeOps all i node ops = ConsNodeOpsM Identity all i node ops
type ConsNodeOpsM m all i node ops = NodeOpsM m all i node
  ( layer :: VariantF all node -> node | ops )

-- Just a way to mutate one layer. Call via `runOverCases` to ensure that
-- structure is being preserved.
type OverCases = OverCasesM Identity
newtype OverCasesM m affected node = OverCasesM
  ((VariantF affected node -> m (VariantF affected node)) -> (node -> m node))

-- Calls `OverCases` where it maps specific cases to the same case using
-- the provided record via `VariantF.mapSomeExpand`; the function will be
-- called on child nodes not covered by the cases.
runOverCases :: forall cases casesrl affected affectedrl unaffected all node.
    RL.RowToList cases casesrl =>
    VariantFMapCases casesrl affected affected node node =>
    RL.RowToList affected affectedrl =>
    VariantTags affectedrl =>
    VariantFMaps affectedrl =>
    R.Union affected unaffected all =>
  OverCases all node ->
  (node -> node) ->
  Record cases -> node -> node
runOverCases (OverCasesM f) rest cases = un Identity <<< f
  (Identity <<< VariantF.over cases rest)

runOverCasesM :: forall cases casesrl affected affectedrl unaffected all node m.
    RL.RowToList cases casesrl =>
    VariantFTraverseCases m casesrl affected affected node node =>
    RL.RowToList affected affectedrl =>
    VariantTags affectedrl =>
    VariantFMaps affectedrl =>
    R.Union affected unaffected all =>
    Applicative m =>
    Traversable (VariantF unaffected) =>
  OverCasesM m all node ->
  (node -> m node) ->
  Record cases -> node -> m node
runOverCasesM (OverCasesM f) rest cases = f (VariantF.traverse cases rest)

-- Eliminate one case of a recursive algebra.
--
-- Essentially constructs a `GenericExprAlgebraVT` given a single `GenericExprAlgebra`.
elim1 ::
  forall sym i v v_ v' v'_ cases casesrl affected affectedrl unaffected all node ops.
    IsSymbol sym =>
    R.Cons sym i v_ v =>
    R.Cons sym i v'_ v' =>
    RL.RowToList cases casesrl =>
    VariantFMapCases casesrl affected affected node node =>
    RL.RowToList affected affectedrl =>
    VariantTags affectedrl =>
    VariantFMaps affectedrl =>
    R.Union affected unaffected all =>
  Proxy sym ->
  (i          ->
  { overlayer :: OverCases all node
  , recurse :: Variant v' -> node -> node
  | ops
  } -> Record cases
  ) ->
  (Variant v_ ->
  { overlayer :: OverCases all node
  , recurse :: Variant v' -> node -> Identity node
  | ops
  } -> (node -> Identity node)) ->
  (Variant v  ->
  { overlayer :: OverCases all node
  , recurse :: Variant v' -> node -> Identity node
  | ops
  } -> (node -> Identity node))
elim1 sym handler = Variant.on sym \i node -> Identity <<<
  runOverCases node.overlayer
    (map (un Identity) $ node.recurse $ Variant.inj sym i)
    (handler i node { recurse = (compose <<< compose) (un Identity) node.recurse})

elim1M ::
  forall sym i v v_ v' v'_ cases casesrl affected affectedrl unaffected all node ops m.
    IsSymbol sym =>
    R.Cons sym i v_ v =>
    R.Cons sym i v'_ v' =>
    RL.RowToList cases casesrl =>
    VariantFTraverseCases m casesrl affected affected node node =>
    RL.RowToList affected affectedrl =>
    VariantTags affectedrl =>
    VariantFMaps affectedrl =>
    R.Union affected unaffected all =>
    Applicative m =>
    Traversable (VariantF unaffected) =>
  Proxy sym ->
  (i          ->
  { overlayer :: OverCasesM m all node
  , recurse :: Variant v' -> node -> m node
  | ops
  } -> Record cases
  ) ->
  (Variant v_ ->
  { overlayer :: OverCasesM m all node
  , recurse :: Variant v' -> node -> m node
  | ops
  } -> (node -> m node)) ->
  (Variant v  ->
  { overlayer :: OverCasesM m all node
  , recurse :: Variant v' -> node -> m node
  | ops
  } -> (node -> m node))
elim1M sym handler = Variant.on sym \i node ->
  runOverCasesM node.overlayer
    (node.recurse $ Variant.inj sym i)
    (handler i node)

-- Run a generic algebra on the plain `Expr` node
runAlgebraExpr :: forall i m a.
  GenericExprAlgebra (ConsNodeOps (AST.ExprLayerRow m a) i (Expr m a) ()) i (Expr m a) ->
  i -> Expr m a -> Expr m a
runAlgebraExpr alg i e = un Identity (runAlgebraExprM alg i e)

runAlgebraExprM :: forall f i m a. Functor f =>
  GenericExprAlgebraM f (ConsNodeOpsM f (AST.ExprLayerRow m a) i (Expr m a) ()) i (Expr m a) ->
  i -> Expr m a -> f (Expr m a)
runAlgebraExprM alg = go where
  go i e = alg i
    { unlayer: project >>> unwrap
    , layer: embed <<< wrap
    , overlayer: OverCasesM (N.under Star _recurse <<< (\f -> map AST.ERVF <<< f <<< un AST.ERVF))
    , recurse: go
    } e

-- Run a generic algebra on an annotated `Noted.Expr` node
runAlgebraNoted :: forall i m a s.
  s ->
  GenericExprAlgebra (ConsNodeOps (AST.ExprLayerRow m a) i (Noted.Expr m s a) ()) i (Noted.Expr m s a) ->
  i -> Noted.Expr m s a -> Noted.Expr m s a
runAlgebraNoted df alg i e = un Identity (runAlgebraNotedM df alg i e)

runAlgebraNotedM :: forall f i m a s. Functor f =>
  s ->
  GenericExprAlgebraM f (ConsNodeOpsM f (AST.ExprLayerRow m a) i (Noted.Expr m s a) ()) i (Noted.Expr m s a) ->
  i -> Noted.Expr m s a -> f (Noted.Expr m s a)
runAlgebraNotedM df alg = go where
  go i e = alg i
    { unlayer: project >>> unwrap >>> extract >>> unwrap
    , layer: embed <<< wrap <<< Tuple df <<< wrap
    , overlayer: OverCasesM (N.under Star _recurse <<< travEnvT <<< (\f -> map AST.ERVF <<< f <<< un AST.ERVF))
    , recurse: go
    } e
  travEnvT f (EnvT (Tuple e x)) = EnvT <<< Tuple e <$> f x

module Dhall.TypeCheck.Universes where

import Prelude

import Data.Array.NonEmpty.Internal (NonEmptyArray(..))
import Data.Either (Either(..))
import Data.Map (SemigroupMap(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Ord.Max (Max(..))
import Data.Set as Set
import Data.Set.NonEmpty (NonEmptySet)
import Data.Set.NonEmpty as NES
import Data.These (theseLeft)
import Data.Tuple (Tuple(..))
import Dhall.Core (Pair(..))
import Dhall.Core.AST.Types (Const(..), Tail(..))
import Dhall.Core.AST.Types.Universes (getTail, onlyConst, onlyTail, onlyVar, onlyVarS, uconst)
import Dhall.Lib.MonoidalState (Discrete(..), DiscreteWithInfos, OccurrencesWithInfos, Total(..), Untotal(..), split)
import Dhall.TypeCheck.UniSolver (Conflict, GESolver(..), closure, substituteConst)

type SolverKey = Const
type SolverVal = Const
type ConstError (l :: Type) = Conflict l
type ConstSolver (l :: Type) = Untotal (Either (Conflict l)) (GESolver l)
type ConstSolved (l :: Type) = GESolver l

unifyConst :: forall l. Semigroup l => l -> Const -> l -> Const -> Maybe (Tuple (ConstSolved l) Const)
unifyConst l1 u1 l2 u2 = map (flip Tuple (u1 <> u2)) $
  let l = l1 <> l2 in
  closure (GESolver $ Map.fromFoldable [Tuple u1 (Tuple l u2), Tuple u2 (Tuple l u1)])

substitute :: forall l. ConstSolved l -> Const -> Const
substitute = const identity

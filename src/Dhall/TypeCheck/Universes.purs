module Dhall.TypeCheck.Universes where

import Prelude

import Data.Map (SemigroupMap(..))
import Data.Map as Map
import Data.Map as Set
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Ord.Max (Max(..))
import Data.Set.NonEmpty (NonEmptySet)
import Data.Set.NonEmpty as NES
import Data.These (theseLeft)
import Data.TraversableWithIndex (forWithIndex)
import Data.Tuple (Tuple(..))
import Dhall.Core.AST.Types (Const(..))
import Dhall.Lib.MonoidalState (Discrete(..), DiscreteWithInfos, OccurrencesWithInfos, Total(..), split)

type SolverKey = String
type SolverVal = Int
type ConstSolver l = SemigroupMap SolverKey (OccurrencesWithInfos l SolverVal)
type ConstSolved l = SemigroupMap SolverKey (DiscreteWithInfos l SolverVal)

getFixed :: Const -> Maybe Int
getFixed (Universes (SemigroupMap us) (Max u)) | Map.isEmpty us = Just u
getFixed _ = Nothing

mkFixed :: Int -> Const
mkFixed = Universes mempty <<< Max

getVariable :: Const -> Maybe (Tuple String Int)
getVariable (Universes (SemigroupMap us) (Max 0))
  | Map.size us == 1, Just { key: k, value: Max v } <- Map.findMin us = Just (Tuple k v)
getVariable _ = Nothing

emit :: forall l. SolverKey -> l -> SolverVal -> ConstSolved l
emit k l v = SemigroupMap $ Map.singleton k $ Tuple
  (Total (pure l))
  (Discrete v)

unifyConst :: forall l. l -> Const -> l -> Const -> Maybe (Tuple (ConstSolved l) Const)
unifyConst _ u1 _ u2 | u1 == u2 = Just (Tuple (SemigroupMap Map.empty) u1)
unifyConst l1 u1 l2 u2 = case getFixed u1, getFixed u2, getVariable u1, getVariable u2 of
  Just v, _, _, Just (Tuple k dv) | v >= dv ->
    Just (Tuple (emit k l1 (v - dv)) (mkFixed v))
  _, Just v, Just (Tuple k dv), _ | v >= dv ->
    Just (Tuple (emit k l2 (v - dv)) (mkFixed v))
  _, _, _, _ -> Nothing

mergeSolvers :: forall l. ConstSolver l -> ConstSolver l -> ConstSolver l
mergeSolvers = append

getErrors :: forall l. ConstSolver l -> Maybe (NonEmptySet SolverKey)
getErrors s =
  case theseLeft (split s) of
    Just es -> NES.fromSet $ Set.keys $ unwrap es
    Nothing -> Nothing

substitute :: forall l. ConstSolved l -> Const -> Const
substitute (SemigroupMap s) (Universes (SemigroupMap us) u) = Universes (SemigroupMap us') u'' where
  Tuple mu' us' = map Map.catMaybes $ forWithIndex us \k (Max dv) ->
    case Map.lookup k s of
      Nothing -> Tuple Nothing (Just (Max dv))
      Just (Tuple _ (Discrete v)) -> Tuple (Just (Max (v + dv))) Nothing
  u'' = case mu' of
    Nothing -> u
    Just u' -> u <> u'

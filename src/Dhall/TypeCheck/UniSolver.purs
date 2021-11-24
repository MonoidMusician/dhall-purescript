module Dhall.TypeCheck.UniSolver where

import Prelude

import Control.Alt ((<|>))
import Data.Either (Either(..))
import Data.Enum (enumFromTo)
import Data.Generic.Rep (class Generic)
import Data.Map (Map, SemigroupMap(..))
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Newtype (class Newtype, over, unwrap)
import Data.NonEmpty (NonEmpty(..), (:|))
import Data.Ord.Max (Max(..))
import Data.Semigroup.Foldable (fold1)
import Data.Show.Generic (genericShow)
import Data.These (These(..))
import Data.Traversable (fold, sequence)
import Data.Tuple (Tuple(..))
import Dhall.Core (Pair(..))
import Dhall.Core.AST.Types (Const(..))
import Dhall.Map as Dhall.Map

mkU :: Array (Tuple String Int) -> Int -> Const
mkU us u = Universes (Map.SemigroupMap (Map.fromFoldable (map (map Max) us))) (Max u)

xy = mkU [Tuple "x" 0, Tuple "y" 0] 0 :: Const
xy1 = mkU [Tuple "x" 0, Tuple "y" 1] 0 :: Const
x2y = mkU [Tuple "x" 2, Tuple "y" 0] 0 :: Const

data Rel
  -- always less than or always greater than
  -- e.g. x < x + 1
  = ALT | AGT
  -- exactly equal
  | EEQ
  -- provably less than or equal / greater than or equal
  -- e.g. x <= max(5, x)
  -- note: this means
  | HLE | HGE
  -- less than or equal, but only equal at small values
  -- (i.e. 0)
  -- e.g. 0 <= y
  | LLE | LGE
  -- uncomparable relation
  -- e.g. x /~ y
  -- e.g. x+5 /~ max(9,x+2)
  | RUN
instance semigroupRel :: Semigroup Rel where
  append RUN _ = RUN
  append _ RUN = RUN
  append EEQ EEQ = EEQ

  append ALT EEQ = HLE
  append EEQ ALT = HLE
  append HLE EEQ = HLE
  append EEQ HLE = HLE
  append LLE EEQ = LLE
  append EEQ LLE = LLE
  append HLE LLE = HLE
  append LLE HLE = HLE
  append ALT ALT = ALT
  append ALT HLE = HLE
  append HLE ALT = HLE
  append ALT LLE = ALT
  append LLE ALT = ALT

  append AGT EEQ = HGE
  append EEQ AGT = HGE
  append HGE EEQ = HGE
  append EEQ HGE = HGE
  append LGE EEQ = LGE
  append EEQ LGE = LGE
  append HGE LGE = HGE
  append LGE HGE = HGE
  append AGT AGT = AGT
  append AGT HGE = HGE
  append HGE AGT = HGE
  append AGT LGE = AGT
  append LGE AGT = AGT

  append _ _ = RUN
derive instance eqRel :: Eq Rel
derive instance ordRel :: Ord Rel
derive instance genericRel :: Generic Rel _
instance showRel :: Show Rel where
  show x = genericShow x

normalizeConst :: Const -> Const
normalizeConst (Universes (SemigroupMap us) u) = Universes (SemigroupMap us) (fold1 $ NonEmpty u us)

downsetMax :: Max Int -> Array (Max Int)
downsetMax (Max u) | u <= zero = pure (Max u)
downsetMax (Max u) = Max <$> (enumFromTo u zero)

downsetConst :: Const -> Array Const
downsetConst (Universes (SemigroupMap us) u) =
  case Map.findMin us of
    Nothing ->
      Universes (SemigroupMap us) <$> downsetMax u
    Just { key: k, value: v } ->
      let
        next = Universes (SemigroupMap (Map.delete k us)) u
      in ado
        v' <- (Just <$> downsetMax v) <|> pure Nothing
        Universes (SemigroupMap us') u' <- downsetConst next
        in Universes (SemigroupMap (maybe identity (Map.insert k) v' us')) u'

bottomConst :: Const
bottomConst = Universes (SemigroupMap Map.empty) (Max zero)

liftRel :: Ordering -> Rel
liftRel EQ = EEQ
liftRel LT = ALT
liftRel GT = AGT

compareConst :: Const -> Const -> Rel
compareConst (Universes us1 u1) (Universes us2 u2) =
  case fold $ Dhall.Map.unionWith compRel (unwrap us1) (unwrap us2), uc of
    Nothing, _ -> ucR
    Just a, _ -> a <> ucR
  where
    uc = u1 `compare` u2
    ucR = liftRel uc
    compRel _ = Just <<< case _ of
      This (Max a) -> Just (if a > 0 then AGT else LGE)
      That (Max a) -> Just (if a > 0 then ALT else LLE)
      Both a b -> Just (liftRel (a `compare` b))

shiftDown :: Int -> Const -> Const
shiftDown d (Universes (SemigroupMap us) (Max u)) =
  Universes (SemigroupMap (map (over Max (_ - d)) us)) (Max (u - d))

-- `shiftLE c1 c2` is the amount to shift `c1` by such that it is always less
-- than or equal to `c2`.
--
-- (c1 +<= c2) # all \d -> shiftDown d c1 <= c2
shiftLE :: Const -> Const -> Maybe (Max Int)
shiftLE (Universes (SemigroupMap us1) (Max u1)) (Universes (SemigroupMap us2) (Max u2)) =
  (fold1 <<< NonEmpty (Max (u1 - u2)))
    <$> sequence (Dhall.Map.unionWith diff us1 us2)
  where
    diff _ = case _ of
      -- fail: the left side contains an extra variable
      This _ -> Just Nothing
      -- do nothing: an extra variable on the right
      That _ -> Nothing
      Both (Max l) (Max r) -> Just (Just (Max (l - r)))

infix 5 shiftLE as +<=

-- A map of GE constraints (key >= value)
newtype GESolver = GESolver (Map Const Const)
derive instance newtypeGESolver :: Newtype GESolver _
derive newtype instance eqGESolver :: Eq GESolver
derive newtype instance showGESolver :: Show GESolver

-- Take one step in closing the GESolver, unless we come across an inconsistency
close :: GESolver -> Either (Pair Const) GESolver
close (GESolver s) = GESolver <$> sequence (Map.mapMaybeWithKey closeKey (map normalizeConst s))
  where
    closeKey k1 v1 =
      let
        mv3 = (\vs -> normalizeConst $ fold1 $ v1 :| vs) <$>
          sequence (Map.mapMaybeWithKey additional s)
        additional k2 v2 =
          case k2 +<= v1 of
            -- Do nothing with this key
            Nothing -> Nothing
            -- reflexivity: add the key itself (k1 >= k1)
            Just _ | k1 == k2 ->
              Just (Just k1)
            -- shift v2 by the amount that makes k2 <= v1 (for transitivity)
            Just (Max d) ->
              let v2d = shiftDown d v2 in
              {-
              case compareConst v2d v1 of
                -- remove this key if it is subsumed by v2d
                AGT -> Just Nothing
                EEQ -> case k1 +<= k2 of
                  Nothing -> Just Nothing
                  Just (Max q) -> let v1q = shiftDown q v1 in
                    case compareConst v2 v1q of
                      AGT -> Just Nothing
                      EEQ | d < 0 -> Just Nothing
                      -- otherwise add v2d to this key
                      _ -> Just (Just v2d)
                -- otherwise add v2d to this key
                _ -> Just (Just v2d)
              -} Just (Just v2d)
      in mv3 <#> \v3 -> case compareConst k1 v3 of
          ALT -> Left (Pair k1 v3)
          _ -> pure v3

closure :: GESolver -> Maybe GESolver
closure s =
  case close s of
    Left _ -> Nothing
    Right s' | s' == s -> Just s
    Right s' -> closure s'

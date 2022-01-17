module Dhall.TypeCheck.UniSolver where

import Prelude

import Data.Array as Array
import Data.Bifunctor (lmap)
import Data.Either (Either(..), isRight, note)
import Data.FoldableWithIndex (foldMapWithIndex, traverseWithIndex_)
import Data.Functor.App (App(..))
import Data.Generic.Rep (class Generic)
import Data.Map (Map, SemigroupMap(..))
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Newtype (class Newtype, over, un, unwrap)
import Data.NonEmpty (NonEmpty(..), (:|))
import Data.Ord.Max (Max(..))
import Data.Semigroup.First (First(..))
import Data.Semigroup.Foldable (fold1)
import Data.Set (Set)
import Data.Set as Set
import Data.Set.NonEmpty (NonEmptySet)
import Data.Set.NonEmpty as NES
import Data.Show.Generic (genericShow)
import Data.These (These(..))
import Data.Traversable (fold, foldMap, sequence)
import Data.Tuple (Tuple(..), curry, uncurry)
import Dhall.Core (Const(..), Pair(..))
import Dhall.Core.AST.Types (Const, Tail(..))
import Dhall.Core.AST.Types.Universes (foundAt, getTail, normalizeConst, onlyConst, onlyTail, onlyVar, reduceByConst', reduceBySelf, uconst, upure, ushift, uvar, uvarS, varsConst)
import Dhall.Map as Dhall.Map

{-
(a; 0) = 0
(a; b+1) = (a, b+1)
(a; b) >= b

(u, v; e) = (u; e), (v; e)
(e; u), (e; v) = (e; u, v)

(l; (e; v)) = (l, e; v) = (l; v), (e; v)

((a; b); c) = ????
c=0: 0
c>0: ((a; b), c)
  b=0: c
  b>0: (a, b, c)

b=0: c
b>0: ((a, b); c)
-}

-- | This semigroup gives information about the relationship of two universe
-- | level expressions across all instantiations of their variables.
-- TODO: use `Maybe Natural` to indicate how high? doesn't seem necessary yet
data Rel
  -- always less than or always greater than
  -- e.g. x < x + 1
  = ALT | AGT
  -- equal variables (arbitrarily large)
  -- (equal constants are `Nothing` in `Maybe Rel`)
  | EEQ
  -- less than or equal/greater than or equal, with equality occurring at
  -- arbitrarily high values
  -- e.g. x <= max(5, x)
  | HLE | HGE
  -- less than or equal, but only equal at small values
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
  append LLE EEQ = HLE
  append EEQ LLE = HLE
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
  append LGE EEQ = HGE
  append EEQ LGE = HGE
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

compareTail :: Tail -> Tail -> Maybe Rel
compareTail (Tail us1 u1) (Tail us2 u2) =
  ucR <> fold (Dhall.Map.unionWith compRel (unwrap us1) (unwrap us2))
  where
    ucR = case u1 `compare` u2 of
      EQ | u1 == Max zero -> Nothing
      EQ -> Just EEQ
      LT -> Just ALT
      GT -> Just AGT
    compRel _ = Just <<< case _ of
      This (Max a) -> Just (if a > 0 then AGT else LGE)
      That (Max a) -> Just (if a > 0 then ALT else LLE)
      Both a b -> Just case a `compare` b of
        EQ -> EEQ
        LT -> ALT
        GT -> AGT

-- FIXME?
compareConst :: Const -> Const -> Maybe Rel
compareConst uz1 uz2 =
  fold $ Dhall.Map.unionWith compRel (unwrap uz1) (unwrap uz2)
  where
    compRel ks _ = Just $ compareTail (foundAt ks uz1) (foundAt ks uz2)

shiftDown :: Int -> Const -> Const
shiftDown d = flip ushift (0 - d)

-- | `shiftLE c1 c2` is the amount to shift `c1` by such that it is always less
-- | than or equal to `c2`.
--
-- (c1 +<= c2) # all \d -> shiftDown d c1 <= c2
shiftLETail :: Tail -> Tail -> Maybe (Max Int)
shiftLETail (Tail (SemigroupMap us1) (Max u1)) (Tail (SemigroupMap us2) (Max u2)) =
  (fold1 <<< NonEmpty (Max (u1 - u2)))
    <$> sequence (Dhall.Map.unionWith diff us1 us2)
  where
    diff _ = case _ of
      -- fail: the left side contains an extra variable
      This _ -> Just Nothing
      -- do nothing: an extra variable on the right
      That _ -> Nothing
      Both (Max l) (Max r) -> Just (Just (Max (l - r)))

shiftLE :: Const -> Const -> Maybe (Max Int)
shiftLE uz1 uz2 =
  fromMaybe (Max zero) <<< foldMap Just <$> sequence (Dhall.Map.unionWith diff (unwrap uz1) (unwrap uz2))
  where
    diff ks _ = Just $ shiftLETail (foundAt ks uz1) (foundAt ks uz2)

infix 5 shiftLE as +<=

-- A map of GE constraints (key >= value)
newtype GESolver = GESolver (Map Const Const)
derive instance newtypeGESolver :: Newtype GESolver _
derive newtype instance eqGESolver :: Eq GESolver
derive newtype instance showGESolver :: Show GESolver

joinbimapGESolver :: (Const -> Const) -> GESolver -> GESolver
joinbimapGESolver f (GESolver s) = GESolver $ un SemigroupMap $
  s # foldMapWithIndex \k v ->
    SemigroupMap $ Map.singleton (f k) (f v)

mapWithIndexGESolver :: (Tuple Const Const -> Tuple Const Const) -> GESolver -> GESolver
mapWithIndexGESolver f (GESolver s) = GESolver $ un SemigroupMap $
  s # foldMapWithIndex \k v ->
    SemigroupMap $ uncurry Map.singleton (curry f k v)

normalizeGESolver :: GESolver -> GESolver
normalizeGESolver = joinbimapGESolver normalizeConst

-- | Determine which variables are known to be positive and known to be zero
-- | and reduce all instances of `imax` which include them accordingly.
reduceImpredicativity :: GESolver -> Either Conflict GESolver
reduceImpredicativity (GESolver s) =
  mustBeZeroM <#> \mustBeZero ->
    joinbimapGESolver (reduce (Tuple mustBeZero mustBePositive)) (GESolver s)
  where
    getZeroesConst level = unwrap >>> unwrap >>> Map.lookup Set.empty >>> maybe mempty (getZeroesTail level)
    getZeroesTail level (Tail (SemigroupMap vs) _) = vs # foldMapWithIndex \var (Max shift) ->
      case compare level shift of
        GT -> mempty
        EQ -> pure (Set.singleton var)
        LT -> App $ Left (Contradiction (Pair (uconst level) (uvarS var shift)))
    mustBeZeroM = un App $ s # foldMapWithIndex \k v ->
      if not onlyTail k then mempty else
      onlyConst (getTail k) # maybe mempty \level ->
        getZeroesConst level v
    mustBePositive = s # foldMapWithIndex \k v ->
      if not onlyTail k then mempty else
      onlyVar (getTail k) # maybe mempty \name ->
        case getTail v of
          Tail _ (Max floor) | floor > zero -> Set.singleton name
          _ -> mempty

-- | For each constraint `k !>= v`, reduce `k` by `v`, and remove it if `k == v`.
reduceKeys :: GESolver -> GESolver
reduceKeys (GESolver kvs) = GESolver $ Map.fromFoldableWith append (Array.mapMaybe reduceKey (Map.toUnfoldableUnordered kvs))
  where
    reduceKey (Tuple k v) =
      let k' = reduceBySelf $ reduceByConst' v k in
      if k' == v then Nothing else
        Just (Tuple k' v)

-- TODO
reduceGESolver :: GESolver -> GESolver
reduceGESolver (GESolver s) = GESolver s

-- | Do one step of the closure algorithm, including normalization steps.
close :: GESolver -> Either Conflict GESolver
close =
  normalizeGESolver >>>
  justClose >=>
  reduceImpredicativity >=>
  reduceKeys >>>
  \s -> reduceGESolver <$> checkImpredicativity s

-- | Take one step in closing the GESolver, unless we come across an inconsistency
justClose :: GESolver -> Either Conflict GESolver
justClose (GESolver s) =
  GESolver <$> sequence (Map.mapMaybeWithKey closeKey (map normalizeConst s))
  where
    closeKey k1 v1 =
      let
        mv3 = (\vs -> normalizeConst $ fold1 $ v1 :| vs) <$>
          sequence (Map.mapMaybeWithKey additional s)
        additional k2 v2 =
          case k2 +<= v1 of
            -- reflexivity: add the key itself (k1 >= k1)
            _ | k1 == k2 ->
              Just (Just k1)
            -- Do nothing with this key
            Nothing -> Nothing
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
          Just ALT -> Left (Contradiction (Pair k1 v3))
          _ -> pure v3

-- | Compute the full closure, if it is consistent.
closure :: GESolver -> Maybe GESolver
closure s =
  case close s of
    Left _ -> Nothing
    Right s' | s' == s -> Just s
    Right s' -> closure s'

-- | Compute the full closure or return an error indicating what the
-- | some contradiction is that prevents it from being consistent.
closure' :: GESolver -> Either Conflict GESolver
closure' s =
  case close s of
    Left e -> Left e
    Right s' | s' == s -> Right s
    Right s' -> closure' s'

powerset :: forall a. Ord a => Set a -> Set (Set a)
powerset vs = case Set.findMin vs of
  Nothing -> Set.singleton Set.empty
  Just v ->
    let
      vs' = Set.delete v vs
      rec = powerset vs'
    in rec <> Set.map (Set.insert v) rec

evaluate' :: Set String -> Const -> Tail
evaluate' vs (Universes (SemigroupMap m)) =
  fromMaybe (Tail mempty (Max zero)) $
    m # foldMapWithIndex \k v ->
      if not Set.subset k vs then mempty else
      Just $ v

evaluate :: Set String -> Const -> Const
evaluate vs = evaluate' vs >>> upure

-- | Reduce a `Const` given what variables must be zero and which must be
-- | positive: discarding hypotheses where some variable is known to be zero
-- | and removing known positive variables from hypotheses.
reduce :: Tuple (Set String) (Set String) -> Const -> Const
reduce (Tuple mustBeZero mustBeNonZero) (Universes (SemigroupMap m)) = Universes $
  m # foldMapWithIndex \k v ->
    if not Set.isEmpty (Set.intersection mustBeZero k)
      then
        mempty
      else
        SemigroupMap $ Map.singleton (Set.difference k mustBeNonZero) $ v

-- | Add to the `GESolver` the constraints the indicate which variables are
-- | zero or positive.
removeImpredicativity :: Tuple (Set String) (Set String) -> GESolver -> GESolver
removeImpredicativity (Tuple mustBeZero mustBeNonZero) (GESolver s) =
  let
    added = (uconst 1 <$ Set.toMap (Set.map uvar mustBeNonZero))
      # if Set.isEmpty mustBeZero then identity else Map.insert (uconst 0) (varsConst mustBeZero)
  in GESolver $ Map.unionWith append added s

-- | Check that some hypothesis is globally satisfiable, and notice which
-- | variables are forced to be zero or positive.
checkImpredicativity :: GESolver -> Either Conflict GESolver
checkImpredicativity (GESolver s) =
  let
    neededCases :: Set String
    neededCases = s # foldMapWithIndex
      \(Universes (SemigroupMap k)) (Universes (SemigroupMap v)) ->
        fold $ Map.keys k <> Map.keys v
    isConsistentWith info =
      isRight $ closure' $ removeImpredicativity info (GESolver s)
    Tuple allowedToBeZero allowedPositive =
      -- Note: this conditional is needed for termination
      if Set.isEmpty neededCases then mempty else
      powerset neededCases # foldMap \assumedPositive ->
        let info = Tuple (Set.difference neededCases assumedPositive) (assumedPositive)
        in if isConsistentWith info
          then info
          else mempty
  in case NES.fromSet (Set.difference neededCases (allowedToBeZero <> allowedPositive)) of
    Just undecided -> Left (Undeterminable undecided)
    Nothing ->
      let
        mustBeNonZero = Set.difference neededCases allowedToBeZero
        mustBeZero = Set.difference neededCases allowedPositive
      in Right $ removeImpredicativity (Tuple mustBeZero mustBeNonZero) (GESolver s)

-- | Concrete assignment of variables to values.
type Solution = Map String Int

substituteTail :: Solution -> Tail -> Tail
substituteTail sol (Tail us u) = (maybe <*> append) (Tail mempty u) $
  us # foldMapWithIndex \k (Max d) -> Just $
    maybe (Tail (SemigroupMap (Map.singleton k (Max d))) (Max zero)) (Tail mempty <<< Max <<< (_ + d)) $
      Map.lookup k sol

substituteHyp :: Solution -> Set String -> Maybe (Set String)
substituteHyp sol = un App <<< foldMap \k -> case Map.lookup k sol of
  Nothing -> App (Just (Set.singleton k))
  Just 0 -> App Nothing
  Just _ -> App (Just Set.empty)

substituteConst :: Solution -> Const -> Const
substituteConst sol (Universes m) = Universes $
  m # foldMapWithIndex \k v ->
    fromMaybe mempty $
      map SemigroupMap $
        Map.singleton <$> substituteHyp sol k <@> substituteTail sol v

data Conflict
  = Contradiction (Pair Const)
  | Undeterminable (NonEmptySet String)
derive instance genericConflict :: Generic Conflict _
instance showConflict :: Show Conflict where
  show = genericShow

substituteSolver :: Solution -> GESolver -> Either Conflict GESolver
substituteSolver sol = map closure' $ over GESolver $ un SemigroupMap <<<
  foldMapWithIndex \k v ->
    SemigroupMap $ Map.singleton (substituteConst sol k) (substituteConst sol v)

data ExError
  = ClosureError Solution GESolver Conflict
  | InternalError Solution GESolver
  | DomainError Const
  | VerifyError Const Const
derive instance genericExError :: Generic ExError _
instance showExError :: Show ExError where
  show = genericShow

unUniverse :: Const -> Maybe Tail
unUniverse c | onlyTail c = pure (getTail c)
unUniverse _ = Nothing

unTail :: Tail -> Maybe Int
unTail (Tail (SemigroupMap m) (Max i)) =
  if Map.isEmpty m then Just i else Nothing

-- | All variables mentioned in the `GESolver`.
gatherVariables :: GESolver -> Set String
gatherVariables (GESolver gm) =
  let
    fromConst (Universes (SemigroupMap m)) =
      m # foldMapWithIndex \k (Tail (SemigroupMap v) _) -> k <> Map.keys v
  in gm # foldMapWithIndex \k v -> fromConst k <> fromConst v

-- | Demonstrate a solution to the `GESolver` (assuming it is already closed).
-- |
-- | The technique is to use closure to tell us lower bounds for variables,
-- | and then pick off a variable or two each time and set it to that lower
-- | bound. Then we reduce the solver state accordingly, run closure again,
-- | and continue onwards.
exemplify :: GESolver -> Either ExError Solution
exemplify ge0 = lmap (ClosureError Map.empty ge0) (closure' ge0) >>= go Map.empty where
  nextStep :: Tail -> Tail -> Maybe (First (Tuple String Int))
  nextStep (Tail (SemigroupMap ks) (Max _atLeast)) (Tail _ (Max floor)) =
    -- Note: atLeast >= floor????
    case Map.findMin ks of
      Just { key: k, value: Max v } -> Just (First (Tuple k (floor - v)))
      Nothing -> Nothing
  getNextStep key value =
    unUniverse key >>= \k ->
    unUniverse value >>= \v ->
      nextStep k v
  go :: Solution -> GESolver -> Either ExError Solution
  go sol0 (GESolver m) = case foldMapWithIndex getNextStep m of
    Nothing -> pure $
      let extra = gatherVariables (GESolver m) in
      Map.union sol0 (zero <$ Set.toMap extra)
    Just (First (Tuple k v)) ->
      let sol = Map.insert k v sol0
      in lmap (ClosureError sol (GESolver m)) (substituteSolver sol (GESolver m)) >>= go sol

-- | Verify a concrete solution to the constraints.
verifySolutionTo :: GESolver -> Solution -> Either ExError Unit
verifySolutionTo (GESolver m) sol = m #
  traverseWithIndex_ \k v -> note (VerifyError k v) $
    unUniverse (substituteConst sol k) >>= unTail >>= \k' ->
      unUniverse (substituteConst sol v) >>= unTail >>= \v' ->
        if k' >= v' then pure unit else Nothing

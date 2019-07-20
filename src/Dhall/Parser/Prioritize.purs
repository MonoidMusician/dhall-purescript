module Dhall.Parser.Prioritize where

import Prelude

import Data.Foldable (class Foldable, fold)
import Data.List (List(..))
import Data.Maybe (Maybe(..), maybe)
import Data.Monoid.Disj (Disj(..))
import Data.Tuple (Tuple(..))
import Dhall.Core.Zippers.Merge (class Merge, mergeWith)
import Matryoshka (class Recursive, project)

-- A partial ordering type, with a result that they are equal, ordered,
-- or uncomparable.
data POrdering = PLT | PEQ | PGT | UNC
derive instance eqPOrdering :: Eq POrdering
instance showPOrdering :: Show POrdering where
  show PLT = "PLT"
  show PEQ = "PEQ"
  show PGT = "PGT"
  show UNC = "UNC"

instance semigroupPOrdering :: Semigroup POrdering where
  append UNC _ = UNC
  append _ UNC = UNC
  append PEQ a = a
  append a PEQ = a
  append PLT PLT = PLT
  append PLT PGT = UNC
  append PGT PLT = UNC
  append PGT PGT = PGT
instance monoidPOrdering :: Monoid POrdering where
  mempty = PEQ

inverse :: POrdering -> POrdering
inverse PLT = PGT
inverse PGT = PLT
inverse PEQ = PEQ
inverse UNC = UNC

symmetricize :: forall t.
  (t -> t -> Maybe POrdering) ->
  (t -> t -> Maybe POrdering)
symmetricize f a b =
  case f a b, f b a of
    -- No result
    Nothing, Nothing -> Nothing
    -- One result
    Just r, Nothing -> Just r
    Nothing, Just r -> Just (inverse r)
    -- Agreeable results
    Just PLT, Just PGT -> Just PLT
    Just PGT, Just PLT -> Just PGT
    Just PEQ, Just PEQ -> Just PEQ
    -- If one side came up as uncomparable,
    -- take the other side instad
    Just r, Just UNC -> Just r
    Just UNC, Just r -> Just (inverse r)
    -- Any other combination is inconsistent/uncomparable
    _, _ -> Just UNC

-- Turn an "is better than" relation into a partial partial ordering.
fromRelation :: forall t.
  (t -> t -> Disj Boolean) ->
  (t -> t -> Maybe POrdering)
fromRelation f = symmetricize \a b ->
  case f a b of
    Disj true -> Just PGT
    Disj false -> Nothing

fromGERelation :: forall t.
  (t -> t -> Boolean) ->
  (t -> t -> POrdering)
fromGERelation f a b =
  case f a b, f b a of
    true, true -> PEQ
    true, false -> PGT
    false, true -> PLT
    false, false -> UNC

fromLRPredicates :: forall t.
  (t -> Boolean) ->
  (t -> Boolean) ->
  (t -> t -> Maybe POrdering)
fromLRPredicates p q = fromRelation \a b -> Disj $ p a && q b

fromPredicate :: forall t.
  (t -> Boolean) ->
  (t -> t -> Maybe POrdering)
fromPredicate p a b = case p a, p b of
  -- both match gives no priority
  true, true -> Nothing
  -- left match gets priority
  true, false -> Just PGT
  -- right match gets priority
  false, true -> Just PLT
  -- no match, no priority
  false, false -> Nothing

-- This ranks two trees based on the given algorithm to rank nodes, which
-- is applied at each necessary level of the tree, top-down, with default
-- behavior of combining results only when the tree shape is comparable
-- (using `Merge`), otherwise stating that they are uncomparable.
--
-- The reason for the comparator returning `Maybe` is to fall back on
-- the default algorithm.
-- The reason for the comparator (potentially) returning `POrdering`
-- is to allow sensible combination of child branches in the default
-- case. (`Ordering` is not enough, because we want the result of
-- `(P)LT <> (P)GT <> (P)LT` to be `UNC`, not `LT`.)
-- It also gives the desired monoid to accumulate prioritizers.
prioritize ::
  forall t f.
    Recursive t f =>
    Merge f =>
    Foldable f =>
  -- Directly compare two trees, or fall back to the default ordering
  (t -> t -> Maybe POrdering) ->
  t -> t -> POrdering
prioritize comparator = go where
  go t1 t2 =
    -- Try the comparator first
    case comparator t1 t2 of
      -- Take its judgment, stop recursing.
      Just r -> r
      -- Otherwise we try to merge, and then fold the results of recursion,
      -- or return that they are uncomparable.
      Nothing ->
        maybe UNC fold (mergeWith go (project t1) (project t2))

-- This knocks out any items judged to be less than another in the list
-- (`EQ` here means to keep both entries).
-- Assumes that the comparator is transitive, but not necessarily
-- symmetric.
roundrobin :: forall a.
  (a -> a -> Ordering) ->
  List a -> List a
roundrobin comparator = go Nil where
  go acc Nil = acc
  go acc (Cons hd tl) =
    let
      -- base case: scanning complete, continue with `go`
      -- with the list of items that survived the comparison
      -- with `hd`.
      scanning Nil rem = Tuple (Cons hd acc) rem
      scanning (Cons hd' tl') rem =
        case comparator hd hd' of
          -- Return immediately, discarding `hd` but
          -- keeping `hd'` in the scanning pool,
          -- which consists of the *scanned* list,
          -- plus `hd'` and the unscanned list `tl'`.
          LT -> Tuple acc (rem <> Cons hd' tl')
          -- Continue to scan, placing `hd'` back
          -- on the list of surviving items
          EQ -> scanning tl' (Cons hd' rem)
          -- Continue to scan, but discarding `hd'`
          -- from the surviving items
          GT -> scanning tl' rem
    in case scanning tl Nil of
      -- manual uncurry for TCO
      Tuple a b -> go a b

isPrioritized ::
  forall t f.
    Recursive t f =>
    Merge f =>
    Foldable f =>
  (t -> t -> Maybe POrdering) ->
  (t -> t -> Boolean)
isPrioritized comparator =
  prioritize comparator >>> compose case _ of
    PGT -> true
    PEQ -> true
    _ -> false

-- Run the roundrobin algorithm on `priorize comparator`.
prioritized ::
  forall t f.
    Recursive t f =>
    Merge f =>
    Foldable f =>
  (t -> t -> Maybe POrdering) ->
  List t -> List t
prioritized comparator =
  roundrobin $ prioritize comparator >>> compose case _ of
    PLT -> LT
    PGT -> GT
    _ -> mempty

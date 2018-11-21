module Dhall.Core.Zippers.Diff where

import Prelude

import Data.Eq (class Eq1)
import Data.Foldable (class Foldable, all, foldMap, foldl, foldr)
import Data.FoldableWithIndex (class FoldableWithIndex, foldMapWithIndex, foldlWithIndex, foldrWithIndex)
import Data.FunctorWithIndex (class FunctorWithIndex, mapWithIndex)
import Data.List (List(..))
import Data.Maybe (Maybe(..))
import Data.Ord (class Ord1)
import Data.Traversable (class Traversable, sequence, traverse)
import Data.TraversableWithIndex (class TraversableWithIndex, traverseWithIndex)
import Dhall.Core.Zippers.Merge (class Merge, mergeWith)
import Matryoshka (class Corecursive, class Recursive, embed, project)

-- | Represent a diff between two recursive trees given by the functor `f`
-- | with data for non-matching cases given by `d` (often something like
-- | `Pair (Mu f)`).
-- |
-- | Based on the `Merge` typeclass, levels of the tree are deemed similar
-- | if they have the same shape, in which case their corresponding children
-- | are diffed recursively; otherwise, the parameter is used to record
-- | how the versions differ.
data Diff f d = Similar (f (Diff f d)) | Different d
derive instance eqDiff :: (Eq1 f, Eq d) => Eq (Diff f d)
derive instance ordDiff :: (Ord1 f, Ord d) => Ord (Diff f d)
derive instance eq1Diff :: Eq1 f => Eq1 (Diff f)
derive instance ord1Diff :: Ord1 f => Ord1 (Diff f)
derive instance functorDiff :: Functor f => Functor (Diff f)
instance functorWithIndexDiff :: FunctorWithIndex i f => FunctorWithIndex (List i) (Diff f) where
    mapWithIndex f (Similar fd) = Similar $ fd # mapWithIndex
      \i -> mapWithIndex \j -> f (Cons i j)
    mapWithIndex f (Different d) = Different (f Nil d)
instance foldableDiff :: Foldable f => Foldable (Diff f) where
  foldMap f (Similar fd) = foldMap (foldMap f) fd
  foldMap f (Different d) = f d
  foldr f b (Similar fd) = foldr (\dd b' -> foldr f b' dd) b fd
  foldr f b (Different d) = f d b
  foldl f b (Similar fd) = foldl (\b' dd -> foldl f b' dd) b fd
  foldl f b (Different d) = f b d
instance foldableWithIndexDiff :: FoldableWithIndex i f => FoldableWithIndex (List i) (Diff f) where
    foldMapWithIndex f (Similar fd) =
      foldMapWithIndex (\i -> foldMapWithIndex (f <<< Cons i)) fd
    foldMapWithIndex f (Different d) = f Nil d
    foldrWithIndex f b (Similar fd) =
      foldrWithIndex (\i dd b' -> foldrWithIndex (f <<< Cons i) b' dd) b fd
    foldrWithIndex f b (Different d) = f Nil d b
    foldlWithIndex f b (Similar fd) =
      foldlWithIndex (\i b' dd -> foldlWithIndex (f <<< Cons i) b' dd) b fd
    foldlWithIndex f b (Different d) = f Nil b d
instance traversableDiff :: Traversable f => Traversable (Diff f) where
  traverse f (Similar fd) = Similar <$> traverse (traverse f) fd
  traverse f (Different d) = Different <$> f d
  sequence (Similar fd) = Similar <$> traverse sequence fd
  sequence (Different d) = Different <$> d
instance traversableWithIndexDiff :: TraversableWithIndex i f => TraversableWithIndex (List i) (Diff f) where
  traverseWithIndex f (Similar fd) = Similar <$>
    traverseWithIndex (\i -> traverseWithIndex (f <<< Cons i)) fd
  traverseWithIndex f (Different d) = Different <$> f Nil d
instance mergeDiff :: (Traversable f, Merge f) => Merge (Diff f) where
  mergeWith f = case _, _ of
    Similar fa, Similar fb ->
      mergeWith (mergeWith f) fa fb >>= sequence >>> map Similar
    Different a, Different b -> Just (Different (f a b))
    _, _ -> Nothing

-- areSame (diff t1 t2) == (t1 == t2)
areSame :: forall f d. Foldable f => Diff f d -> Boolean
areSame (Similar shape) = all areSame shape
areSame (Different _) = false

-- | Compute the diff based on the `Merge` instance, combining the non-matching
-- | nodes with the provided function (often just `Pair` or `Tuple`,
-- | but it could return more specialized diff data too).
diffWith ::
  forall t f d.
    Recursive t f =>
    Merge f =>
  (t -> t -> d) ->
  t -> t -> Diff f d
diffWith f t1 t2 =
  case mergeWith (diffWith f) (project t1) (project t2) of
    Nothing -> Different (f t1 t2)
    Just shape -> Similar shape

-- | Recover the original shape of the input data given a projection
-- | from the values stored in the functor to the original tree type.
recover :: forall f t d. Corecursive t f => (d -> t) -> Diff f d -> t
recover f (Similar shape) = embed (recover f <$> shape)
recover f (Different d) = f d

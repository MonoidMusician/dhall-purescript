module Dhall.Lib.Timeline where

import Prelude

import Control.Comonad (class Comonad)
import Control.Extend (class Extend)
import Control.Plus (empty, (<|>))
import Data.Eq (class Eq1)
import Data.Foldable (class Foldable, foldMap, foldl, foldr)
import Data.FoldableWithIndex (class FoldableWithIndex, foldMapWithIndex, foldlWithIndex, foldrWithIndex)
import Data.FunctorWithIndex (class FunctorWithIndex, mapWithIndex)
import Data.List (List(..), (:))
import Data.List as List
import Data.List.Types (NonEmptyList(..))
import Data.Maybe (Maybe(..))
import Data.Monoid.Dual (Dual(..))
import Data.Newtype (un)
import Data.NonEmpty ((:|))
import Data.Ord (class Ord1)
import Data.Semigroup.Foldable (class Foldable1, foldl1Default, foldr1Default)
import Data.Traversable (class Traversable, sequence, traverse)
import Data.TraversableWithIndex (class TraversableWithIndex, traverseWithIndex)
import Dhall.Lib.DualAp (DualAp(..))

data Timeline a = Timeline (List a) a (List a)
derive instance eqTimeline :: Eq a => Eq (Timeline a)
derive instance ordTimeline :: Ord a => Ord (Timeline a)
derive instance eq1Timeline :: Eq1 Timeline
derive instance ord1Timeline :: Ord1 Timeline
derive instance functorTimeline :: Functor Timeline
instance functorWithIndexTimeline :: FunctorWithIndex Int Timeline where
  mapWithIndex f (Timeline p a n) = Timeline
    (mapWithIndex (f <<< negate <<< add one) p)
    (f zero a)
    (mapWithIndex (f <<< add one) n)
-- Some instances adapted from https://github.com/paluh/purescript-pointed-list/blob/v0.3.0/src/Data/List/Pointed.purs
instance foldableTimeline :: Foldable Timeline where
  foldr f z (Timeline p a n) =
    foldl (flip f) (f a (foldr f z n)) p

  foldl f z (Timeline p a n) =
    foldl f (f (foldr (flip f) z p) a) n

  foldMap f (Timeline p a n) =
    un Dual (foldMap (Dual <<< f) p) <> f a <> foldMap f n
instance foldableWithIndexTimeline :: FoldableWithIndex Int Timeline where
  foldrWithIndex f z (Timeline p a n) =
    foldlWithIndex (flip <<< f <<< negate <<< add one) (f zero a (foldrWithIndex (f <<< add one) z n)) p

  foldlWithIndex f z (Timeline p a n) =
    foldlWithIndex (f <<< add one) (f zero (foldrWithIndex (flip <<< f <<< negate <<< add one) z p) a) n

  foldMapWithIndex f (Timeline p a n) =
    un Dual (foldMapWithIndex (compose Dual <<< f <<< negate <<< add one) p) <> f zero a <> foldMapWithIndex (f <<< add one) n
instance traversableTimeline :: Traversable Timeline where
  traverse f (Timeline p a n) = Timeline
    <$> (un DualAp $ traverse (DualAp <<< f) p)
    <*> f a
    <*> traverse f n
  sequence (Timeline p a n) = Timeline
    <$> (un DualAp $ traverse DualAp p)
    <*> a <*> sequence n
instance traversableWithIndexTimeline :: TraversableWithIndex Int Timeline where
  traverseWithIndex f (Timeline p a n) = Timeline
    <$> (un DualAp $ traverseWithIndex (compose DualAp <<< f <<< negate <<< add one) p)
    <*> f zero a
    <*> traverseWithIndex (f <<< add one) n
instance foldable1Timeline :: Foldable1 Timeline where
  foldl1 a = foldl1Default a
  foldr1 a = foldr1Default a
  foldMap1 f (Timeline p a n) =
    foldl (\r e → r <> f e) (foldl (\r e → f e <> r) (f a) p) n
instance extendTimeline :: Extend Timeline where
  extend f z@(Timeline p a n) = Timeline
      (gather (a : n) p <#> \(Timeline n' a' p') -> f (Timeline p' a' n'))
      (f z)
      (gather (a : p) n <#> \(Timeline p' a' n') -> f (Timeline p' a' n'))
    where
      gather :: forall a. List a -> List a -> List (Timeline a)
      gather passed Nil = Nil
      gather passed (a' : a's) =
          Timeline passed a' a's : gather (a' : passed) a's
instance comonadTimeline :: Comonad Timeline where
  extract (Timeline _ a _) = a
instance applyTimeline :: Apply Timeline where
  apply = ap
instance applicativeTimeline :: Applicative Timeline where
  pure a = Timeline empty a empty
-- Untested, but I think it should work and obey laws?
instance bindTimeline :: Bind Timeline where
  bind (Timeline p a n) f = case f a of
    Timeline p' a' n' -> Timeline
      ((p >>= f >>> ahistorical >>> List.reverse) <|> p')
      a'
      (n' <|> (n >>= f >>> ahistorical))
instance monadTimeline :: Monad Timeline

ahistorical :: Timeline ~> List
ahistorical (Timeline p a n) = List.reverse p <|> pure a <|> n

neahistorical :: Timeline ~> NonEmptyList
neahistorical (Timeline p a n) = NonEmptyList case List.reverse p of
  Nil -> a :| n
  h : t -> h :| (t <|> pure a <|> n)

happen :: forall a. a -> Timeline a -> Timeline a
happen a' (Timeline p a _) = Timeline (a : p) a' empty

unhappen :: forall a. Timeline a -> Maybe (Timeline a)
unhappen (Timeline Nil _ _) = Nothing
unhappen (Timeline (a' : p) a n) = Just (Timeline p a' (a : n))

rehappen :: forall a. Timeline a -> Maybe (Timeline a)
rehappen (Timeline _ _ Nil) = Nothing
rehappen (Timeline p a (a' : n)) = Just (Timeline (a : p) a' n)

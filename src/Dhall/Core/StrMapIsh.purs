module Dhall.Core.StrMapIsh where

import Prelude

import Control.Extend (extend)
import Data.Array as Array
import Data.Eq (class Eq1)
import Data.Foldable (class Foldable, find, foldMap, foldl, foldr)
import Data.FoldableWithIndex (class FoldableWithIndex)
import Data.Function (on)
import Data.Functor.Compose (Compose(..))
import Data.FunctorWithIndex (class FunctorWithIndex)
import Data.Lens (Prism', prism')
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, fromMaybe')
import Data.Newtype (class Newtype, over, unwrap, wrap)
import Data.Ord (class Ord1)
import Data.Traversable (class Traversable, traverse)
import Data.TraversableWithIndex (class TraversableWithIndex)
import Data.Tuple (Tuple(..), fst, snd, uncurry)
import Data.Unfoldable (class Unfoldable)

-- This abstracts the functor used for record and union cases in the AST
-- (the major difference being that sometimes we want sorting vs ordering)
class (Ord1 m, TraversableWithIndex String m) <= StrMapIsh m where
  empty :: forall a. m a
  isEmpty :: forall a. m a -> Boolean
  get :: forall a. String -> m a -> Maybe a
  modify :: forall a. String -> (a -> Tuple String a) -> m a -> Maybe (m a)
  alter :: forall a. String -> (Maybe a -> Maybe a) -> m a -> m a
  delete :: forall a. String -> m a -> Maybe (m a)
  unionWith :: forall a. (a -> a -> a) -> m a -> m a -> m a
  toUnfoldable :: forall f a. Unfoldable f => m a -> f (Tuple String a)
  fromFoldable :: forall f a. Foldable f => f (Tuple String a) -> m a

instance strMapMapString :: StrMapIsh (Map String) where
  empty = Map.empty
  isEmpty = Map.isEmpty
  get = Map.lookup
  modify k f m = do
    v <- Map.lookup k m
    let Tuple k' v' = f v
    let m' = if k == k' then m else Map.delete k m
    pure $ Map.insert k' v' m'
  alter = flip Map.alter
  delete k m = Map.lookup k m $> Map.delete k m
  unionWith = Map.unionWith
  toUnfoldable = Map.toUnfoldable
  fromFoldable = Map.fromFoldable

newtype InsOrdStrMap a = InsOrdStrMap (Compose Array (Tuple String) a)
derive instance newtypeIOSM :: Newtype (InsOrdStrMap a) _
derive newtype instance eqIOSM :: Eq a => Eq (InsOrdStrMap a)
derive newtype instance ordIOSM :: Ord a => Ord (InsOrdStrMap a)
derive newtype instance eq1IOSM :: Eq1 InsOrdStrMap
derive newtype instance ord1IOSM :: Ord1 InsOrdStrMap
mkIOSM :: forall a. Array (Tuple String a) -> InsOrdStrMap a
mkIOSM = InsOrdStrMap <<< Compose
unIOSM :: forall a. InsOrdStrMap a -> Array (Tuple String a)
unIOSM (InsOrdStrMap (Compose as)) = as
derive newtype instance functorIOSM :: Functor InsOrdStrMap
derive newtype instance foldableIOSM :: Foldable InsOrdStrMap
derive newtype instance traversableIOSM :: Traversable InsOrdStrMap
instance functorWithIndexIOSM :: FunctorWithIndex String InsOrdStrMap where
  mapWithIndex f = over InsOrdStrMap $ over Compose $ map $ extend $ uncurry f
instance foldableWithIndexIOSM :: FoldableWithIndex String InsOrdStrMap where
  foldMapWithIndex f = unwrap >>> unwrap >>> foldMap (uncurry f)
  foldrWithIndex f b0 = unwrap >>> unwrap >>> foldr (uncurry f) b0
  foldlWithIndex f b0 = unwrap >>> unwrap >>> foldl (flip (uncurry (flip <<< f))) b0
instance traversableWithIndexIOSM :: TraversableWithIndex String InsOrdStrMap where
  traverseWithIndex f = unwrap >>> unwrap >>>
    traverse (\(Tuple k v) -> f k v <#> Tuple k) >>> map (wrap >>> wrap)
instance strMapIshIOSM :: StrMapIsh InsOrdStrMap where
  empty = wrap $ wrap []
  isEmpty = unwrap >>> unwrap >>> Array.null
  get k = unwrap >>> unwrap >>> find (fst >>> eq k) >>> map snd
  modify k f (InsOrdStrMap (Compose as)) = wrap <<< wrap <$> do
    i <- Array.findIndex (fst >>> eq k) as
    Array.modifyAt i ((=<<) f) as
  alter k f (InsOrdStrMap (Compose as)) = wrap $ wrap $
    case Array.findIndex (fst >>> eq k) as of
      Nothing -> case f Nothing of
        Nothing -> as
        Just v -> [Tuple k v] <> as
      Just i -> (fromMaybe <*> Array.alterAt i (traverse (f <<< Just))) as
  delete k (InsOrdStrMap (Compose as)) = wrap <<< wrap <$> do
    i <- Array.findIndex (fst >>> eq k) as
    Array.deleteAt i as
  unionWith combine (InsOrdStrMap (Compose l')) (InsOrdStrMap (Compose r')) =
    let
      l = Array.nubBy (compare `on` fst) l'
      r = Array.nubBy (compare `on` fst) r'
      inserting as (Tuple k v) = fromMaybe' (\_ -> as <> [Tuple k v]) do
        i <- Array.findIndex (fst >>> eq k) as
        Array.modifyAt i (map (combine <@> v)) as
    in wrap $ wrap $ Array.foldl inserting l r
  toUnfoldable = unwrap >>> unwrap >>> Array.toUnfoldable
  fromFoldable = wrap <<< wrap <<< Array.nubBy (compare `on` fst) <<< Array.fromFoldable

-- FIXME: I don't think this is what I want for this name?
set :: forall m a. StrMapIsh m => String -> a -> m a -> Maybe (m a)
set k v = modify k (pure (Tuple k v))

insert :: forall m a. StrMapIsh m => String -> a -> m a -> m a
insert k v = alter k (pure (pure v))

singleton :: forall m a. StrMapIsh m => String -> a -> m a
singleton k v = insert k v empty

_Empty :: forall m a. StrMapIsh m => Prism' (m a) Unit
_Empty = prism' (const empty)
  \m -> if isEmpty m then Just unit else Nothing

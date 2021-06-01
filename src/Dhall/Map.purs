module Dhall.Map where

import Prelude

import Control.Alt (class Alt)
import Control.Comonad (extract)
import Control.Extend (extend)
import Control.Plus (class Plus)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Eq (class Eq1)
import Data.Foldable (class Foldable, find, foldMap, foldl, foldr)
import Data.FoldableWithIndex (class FoldableWithIndex)
import Data.Function (on)
import Data.Functor.Compose (Compose(..))
import Data.FunctorWithIndex (class FunctorWithIndex)
import Data.Lens (Prism', prism')
import Data.List (List)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, fromMaybe', isJust)
import Data.Newtype (class Newtype, over, unwrap, wrap)
import Data.Ord (class Ord1)
import Data.These (These(..))
import Data.Traversable (class Traversable, traverse)
import Data.TraversableWithIndex (class TraversableWithIndex)
import Data.Tuple (Tuple(..), fst, snd, uncurry)
import Data.Unfoldable (class Unfoldable)
import Type.Proxy (Proxy2(..))

-- This abstracts the functor used for record and union cases in the AST
-- (the major difference being that sometimes we want sorting vs ordering)
class (Ord k, Ord1 m, TraversableWithIndex k m) <= MapLike k m | m -> k where
  empty :: forall a. m a
  isEmpty :: forall a. m a -> Boolean
  get :: forall a. k -> m a -> Maybe a
  modify :: forall a. k -> (a -> Tuple k a) -> m a -> Maybe (m a)
  alter :: forall a. k -> (Maybe a -> Maybe a) -> m a -> m a
  delete :: forall a. k -> m a -> Maybe (m a)
  unionWith :: forall a b c. (k -> These a b -> Maybe c) -> m a -> m b -> m c
  toUnfoldable :: forall f a. Unfoldable f => m a -> f (Tuple k a)
  fromFoldable :: forall f a. Foldable f => f (Tuple k a) -> m a
  size :: forall a. m a -> Int

symmetricDiff :: forall k m a b. MapLike k m => m a -> m b -> m (Either a b)
symmetricDiff = unionWith \_ -> case _ of
  Both _ _ -> Nothing
  This a -> Just (Left a)
  That b -> Just (Right b)

-- | This is how I think a union of two maps is most properly defined ...
unionWithMapThese :: forall k a b c. Ord k =>
  (k -> These a b -> Maybe c) ->
  Map k a -> Map k b -> Map k c
unionWithMapThese f ma mb =
  let
    combine = case _, _ of
      This a, That b -> Both a b
      That b, This a -> Both a b
      Both a b, _ -> Both a b
      This a, Both _ b -> Both a b
      That b, Both a _ -> Both a b
      That b, That _ -> That b
      This a, This _ -> This a
  in Map.mapMaybeWithKey f $ Map.unionWith combine (This <$> ma) (That <$> mb)

instance strMapMapString :: Ord k => MapLike k (Map k) where
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
  unionWith = unionWithMapThese
  toUnfoldable = Map.toUnfoldable
  fromFoldable = Map.fromFoldable
  size = Map.size

newtype InsOrdMap k a = InsOrdMap (Compose Array (Tuple k) a)
type InsOrdStrMap = InsOrdMap String
derive instance newtypeIOSM :: Newtype (InsOrdMap k a) _
derive newtype instance eqIOSM :: (Eq k, Eq a) => Eq (InsOrdMap k a)
derive newtype instance ordIOSM :: (Ord k, Ord a) => Ord (InsOrdMap k a)
derive newtype instance eq1IOSM :: Eq k => Eq1 (InsOrdMap k)
derive newtype instance ord1IOSM :: Ord k => Ord1 (InsOrdMap k)
mkIOSM :: forall k a. Array (Tuple k a) -> InsOrdMap k a
mkIOSM = InsOrdMap <<< Compose
unIOSM :: forall k a. InsOrdMap k a -> Array (Tuple k a)
unIOSM (InsOrdMap (Compose as)) = as
derive newtype instance functorIOSM :: Functor (InsOrdMap k)
derive newtype instance foldableIOSM :: Foldable (InsOrdMap k)
derive newtype instance traversableIOSM :: Traversable (InsOrdMap k)
derive newtype instance altIOSM :: Alt (InsOrdMap k)
derive newtype instance plusIOSM :: Plus (InsOrdMap k)
instance functorWithIndexIOSM :: FunctorWithIndex k (InsOrdMap k) where
  mapWithIndex f = over InsOrdMap $ over Compose $ map $ extend $ uncurry f
instance foldableWithIndexIOSM :: FoldableWithIndex k (InsOrdMap k) where
  foldMapWithIndex f = unwrap >>> unwrap >>> foldMap (uncurry f)
  foldrWithIndex f b0 = unwrap >>> unwrap >>> foldr (uncurry f) b0
  foldlWithIndex f b0 = unwrap >>> unwrap >>> foldl (flip (uncurry (flip <<< f))) b0
instance traversableWithIndexIOSM :: TraversableWithIndex k (InsOrdMap k) where
  traverseWithIndex f = unwrap >>> unwrap >>>
    traverse (\(Tuple k v) -> f k v <#> Tuple k) >>> map (wrap >>> wrap)
instance strMapIshIOSM :: Ord k => MapLike k (InsOrdMap k) where
  empty = wrap $ wrap []
  isEmpty = unwrap >>> unwrap >>> Array.null
  get k = unwrap >>> unwrap >>> find (fst >>> eq k) >>> map snd
  modify k f (InsOrdMap (Compose as)) = wrap <<< wrap <$> do
    i <- Array.findIndex (fst >>> eq k) as
    Array.modifyAt i (f <<< extract) as
  alter k f (InsOrdMap (Compose as)) = wrap $ wrap $
    case Array.findIndex (fst >>> eq k) as of
      Nothing -> case f Nothing of
        Nothing -> as
        Just v -> [Tuple k v] <> as
      Just i -> (fromMaybe <*> Array.alterAt i (traverse (f <<< Just))) as
  delete k (InsOrdMap (Compose as)) = wrap <<< wrap <$> do
    i <- Array.findIndex (fst >>> eq k) as
    Array.deleteAt i as
  unionWith f (InsOrdMap (Compose l')) (InsOrdMap (Compose r')) =
    let
      combine = case _, _ of
        This a, That b -> Both a b
        That b, This a -> Both a b
        Both a b, _ -> Both a b
        This a, Both _ b -> Both a b
        That b, Both a _ -> Both a b
        That b, That _ -> That b
        This a, This _ -> This a
      l = Array.nubBy (compare `on` fst) l'
      r = Array.nubBy (compare `on` fst) r'
      inserting as (Tuple k v) = fromMaybe' (\_ -> as <> [Tuple k v]) do
        i <- Array.findIndex (fst >>> eq k) as
        Array.modifyAt i (map (combine <@> v)) as
      finalize = Array.mapMaybe (\(Tuple k v) -> Tuple k <$> f k v)
    in mkIOSM $ finalize $
      Array.foldl inserting (map This <$> l) (map That <$> r)
  toUnfoldable = unIOSM >>> Array.toUnfoldable
  fromFoldable = mkIOSM <<< Array.nubBy (compare `on` fst) <<< Array.fromFoldable
  size = unIOSM >>> Array.length

-- FIXME: I don't think this is what I want for this name?
set :: forall k m a. MapLike k m => k -> a -> m a -> Maybe (m a)
set k v = modify k (pure (Tuple k v))

has :: forall k m a. MapLike k m => k -> m a -> Boolean
has k vs = isJust (get k vs)

insert :: forall k m a. MapLike k m => k -> a -> m a -> m a
insert k v = alter k (pure (pure v))

singleton :: forall k m a. MapLike k m => k -> a -> m a
singleton k v = insert k v empty

_Empty :: forall k m a. MapLike k m => Prism' (m a) Unit
_Empty = prism' (const empty)
  \m -> if isEmpty m then Just unit else Nothing

conv :: forall k m m'. MapLike k m => MapLike k m' => m ~> m'
conv = toUnfoldable >>> (identity :: List ~> List) >>> fromFoldable

unordered :: forall k m. MapLike k m => m ~> Map k
unordered = conv

convTo :: forall k m m'. MapLike k m => MapLike k m' => Proxy2 m' -> m ~> m'
convTo Proxy2 = conv

toUnfoldableSorted :: forall k m f a. MapLike k m => Unfoldable f =>
  m a -> f (Tuple k a)
toUnfoldableSorted = unordered >>> toUnfoldable

module Dhall.Core.Zippers.Merge where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NonEmptyArray
import Data.Const (Const(..))
import Data.Either (Either(..))
import Data.Functor.Compose (Compose(..))
import Data.Functor.Coproduct (Coproduct(..))
import Data.Functor.Product (Product(..))
import Data.Identity (Identity(..))
import Data.List (List(..))
import Data.Maybe (Maybe(..))
import Data.NonEmpty (NonEmpty, (:|))
import Data.Traversable (class Traversable, sequence)
import Data.Tuple (Tuple(..))

-- Zip two functors only iff they have identical shapes.
-- That is, they must contain values at exactly the same "positions",
-- and any other values in their structure must also be identical.
--
-- Laws:
--   - Idempotent:
--       merge fa fa == Just $ fa <#> \a -> Tuple a a
--   - Commutative:
--       mergeWith f fa fb == mergeWith (flip f) fb fa
--   - Partial inverse:
--       Just fc = merge fa fb implies that
--         fc <#> fst == fa (and thus that fc <#> snd = fb)
--   - Given Distributive f =>
--       mergeWith f fa fb = Just (zipWithOf cotraversed f fa fb)
--
--   - (Tentative) Given Eq i and TraversableWithIndex i f =>
--       merge fa fb = Just fc =>
--       (traverseWithIndex \i a -> Tuple a <#> elementByIndex i fb) fa = Just fc
--     where elementByIndex :: i -> f b -> Maybe b
class Functor f <= Merge f where
  mergeWith :: forall a b c. (a -> b -> c) -> f a -> f b -> Maybe (f c)

merge :: forall f a b. Merge f => f a -> f b -> Maybe (f (Tuple a b))
merge = mergeWith Tuple

instance mergeIdentity :: Merge Identity where
  mergeWith f (Identity a) (Identity b) = Just (Identity (f a b))
instance mergeConst :: Eq a => Merge (Const a) where
  mergeWith _ (Const l) (Const r) =
    if l == r then Just (Const l) else Nothing
instance mergeTuple :: Eq a => Merge (Tuple a) where
  mergeWith f (Tuple l a) (Tuple r b) =
    if l == r then Just (Tuple l (f a b)) else Nothing
instance mergeMaybe :: Merge Maybe where
  mergeWith f = case _, _ of
    Just a, Just b -> Just (Just (f a b))
    Nothing, Nothing -> Just Nothing
    _, _ -> Nothing
instance mergeEither :: Eq a => Merge (Either a) where
  mergeWith f = case _, _ of
    Left a, Left b | a == b -> Just (Left a)
    Right a, Right b -> Just (Right (f a b))
    _, _ -> Nothing
instance mergeList :: Merge List where
  mergeWith f = case _, _ of
    Cons a fa, Cons b fb -> Cons (f a b) <$> mergeWith f fa fb
    Nil, Nil -> Just Nil
    _, _ -> Nothing
instance mergeNonEmpty :: Merge f => Merge (NonEmpty f) where
  mergeWith f (a :| fa) (b :| fb) = (f a b :| _) <$> mergeWith f fa fb
instance mergeArray :: Merge Array where
  mergeWith f a b
    | Array.length a == Array.length b
    = Just (Array.zipWith f a b)
  mergeWith _ _ _ = Nothing
instance mergeNonEmptyArray :: Merge NonEmptyArray where
  mergeWith f a b
    | NonEmptyArray.length a == NonEmptyArray.length b
    = Just (NonEmptyArray.zipWith f a b)
  mergeWith _ _ _ = Nothing
instance mergeProduct :: (Merge f, Merge g) => Merge (Product f g) where
  mergeWith f (Product (Tuple fa ga)) (Product (Tuple fb gb)) =
    Product <$> (Tuple <$> mergeWith f fa fb <*> mergeWith f ga gb)
instance mergeCoproduct :: (Merge f, Merge g) => Merge (Coproduct f g) where
  mergeWith f (Coproduct ca) (Coproduct cb) = case ca, cb of
    Left fa, Left fb -> Coproduct <<< Left <$> mergeWith f fa fb
    Right ga, Right gb -> Coproduct <<< Right <$> mergeWith f ga gb
    _, _ -> Nothing
instance mergeCompose :: (Traversable f, Merge f, Merge g) => Merge (Compose f g) where
  mergeWith f (Compose fga) (Compose fgb) =
    map Compose <<< sequence =<< mergeWith (mergeWith f) fga fgb

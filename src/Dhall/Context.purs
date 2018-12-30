module Dhall.Context where

import Prelude

import Data.Foldable (class Foldable, fold, foldMap, foldl, foldr)
import Data.FoldableWithIndex (class FoldableWithIndex)
import Data.Functor.Compose (Compose(..))
import Data.FunctorWithIndex (class FunctorWithIndex, mapWithIndex)
import Data.List (List(..), (:))
import Data.List as List
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (class Newtype, unwrap)
import Data.Traversable (class Traversable, sequence, traverse)
import Data.TraversableWithIndex (class TraversableWithIndex)
import Data.Tuple (Tuple(..))
import Dhall.Core.AST.Types (Var(..))

-- | A `Context a` associates `Text` labels with values of type `a`.  Each
-- | `Text` label can correspond to multiple values of type `a`
-- | The `Context` is used for type-checking when `a = Expr X`
-- | * You create a `Context` using `empty` and `insert`
-- | * You transform a `Context` using `fmap`
-- | * You consume a `Context` using `lookup` and `toList`
-- | The difference between a `Context` and a `Data.Map.Map` is that a `Context`
-- | lets you have multiple ordered occurrences of the same key and you can
-- | query for the `n`th occurrence of a given key.
newtype Context a = Context (List (Tuple String a))
derive instance newtypeContext :: Newtype (Context a) _
derive instance functorContext :: Functor Context
instance foldableContext :: Foldable Context where
  foldMap f = foldMap f <<< Compose <<< unwrap
  foldr f c = foldr f c <<< Compose <<< unwrap
  foldl f c = foldl f c <<< Compose <<< unwrap
instance traversableContext :: Traversable Context where
  traverse f (Context as) = Context <$> traverse (traverse f) as
  sequence (Context as) = Context <$> traverse sequence as
instance functorWithIndexContext :: FunctorWithIndex Var Context where
  mapWithIndex f = go Map.empty where
    go _ (Context Nil) = Context Nil
    go ks (Context (Tuple k v : kvs)) =
      let
        n = fromMaybe zero $ Map.lookup k ks
        ks' = Map.insert k (n+one) ks
        Context kvs' = go ks' (Context kvs)
      in Context (Tuple k (f (V k n) v) : kvs')
instance foldableWithIndexContext :: FoldableWithIndex Var Context where
  foldMapWithIndex f = fold <<< mapWithIndex f
  foldrWithIndex f c = foldr ($) c <<< mapWithIndex f
  foldlWithIndex f c = foldl (#) c <<< mapWithIndex (flip <<< f)
instance traversableWithIndexContext :: TraversableWithIndex Var Context where
  traverseWithIndex f = sequence <<< mapWithIndex f

-- | An empty context with no key-value pairs
empty :: forall a. Context a
empty = Context Nil

-- | Add a key-value pair to the `Context`
insert :: forall a. String -> a -> Context a -> Context a
insert k v (Context kvs) = Context (Tuple k v : kvs)

-- | "Pattern match" on a `Context`
-- | ```purescript
-- | match (insert k v ctx) = Just (k, v, ctx)
-- | match  empty           = Nothing
-- | ```
match :: forall a.
  Context a ->
  Maybe { key :: String, value :: a, context :: Context a }
match (Context (Tuple key value : context)) = Just
  { key, value, context: Context context }
match (Context Nil) = Nothing

-- | Look up a key by name and index
-- | ```purescript
-- | lookup _ _         empty  = Nothing
-- | lookup k 0 (insert k v c) = Just v
-- | lookup k n (insert k v c) = lookup k (n - 1) c
-- | lookup k n (insert j v c) = lookup k  n      c  -- k /= j
-- | ```
lookup :: forall a. String -> Int -> Context a -> Maybe a
lookup _ _ (Context         Nil  ) =
    Nothing
lookup x n (Context (Tuple k v : kvs)) =
    if x == k
    then if n == 0
         then Just v
         else lookup x (n - 1) (Context kvs)
    else lookup x n (Context kvs)

-- | Lookup a entry by name and index, returning its value and absolute depth.
lookupDepth :: forall a. String -> Int -> Context a -> Maybe (Tuple Int a)
lookupDepth x = go 0 where
  go _ _ (Context         Nil  ) =
    Nothing
  go i n (Context (Tuple k v : kvs)) =
    if x == k
    then if n == 0
         then Just (Tuple i v)
         else go (i+1) (n - 1) (Context kvs)
    else go (i+1) n (Context kvs)

-- | Return all key-value associations as a list
-- | ```purescript
-- | toList           empty  = []
-- | toList (insert k v ctx) = (k, v) : toList ctx
-- | ```
toList :: forall a. Context a -> List (Tuple String a)
toList (Context l) = l

mapMaybe :: forall a b. (a -> Maybe b) -> Context a -> Context b
mapMaybe f (Context l) = Context (List.mapMaybe (traverse f) l)

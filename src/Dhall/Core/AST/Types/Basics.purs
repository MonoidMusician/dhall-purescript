module Dhall.Core.AST.Types.Basics where

import Prelude

import Data.Const (Const)
import Data.Const as ConstF
import Data.Eq (class Eq1)
import Data.Foldable (class Foldable, foldMap, foldl, foldr)
import Data.FoldableWithIndex (class FoldableWithIndex, foldMapWithIndex, foldlWithIndex, foldrWithIndex)
import Data.FunctorWithIndex (class FunctorWithIndex, mapWithIndex)
import Data.Maybe (Maybe)
import Data.Natural (Natural)
import Data.Ord (class Ord1)
import Data.Traversable (class Traversable, sequence, traverse)
import Data.TraversableWithIndex (class TraversableWithIndex, traverseWithIndex)
import Data.Variant.Internal (FProxy)

-- This file defines basic functor types used in the AST definition

-- Convenience synonyms
type CONST a = FProxy (ConstF.Const a)
type UNIT = CONST Unit
type VOID = CONST Void

-- | Index type for `Triplet` functor below
data Three = Three1 | Three2 | Three3
derive instance eqThree :: Eq Three
derive instance ordThree :: Ord Three

type Maybe' = Const Unit

data Pair a = Pair a a
derive instance eqPair :: Eq a => Eq (Pair a)
derive instance ordPair :: Ord a => Ord (Pair a)
derive instance eq1Pair :: Eq1 Pair
derive instance ord1Pair :: Ord1 Pair

instance functorPair :: Functor Pair where
  map f (Pair a0 a1) = Pair (f a0) (f a1)

instance functorWithIndexPair :: FunctorWithIndex (Boolean) Pair where
  mapWithIndex f (Pair a0 a1) = Pair (f false a0) (f true a1)

instance foldablePair :: Foldable Pair where
  foldMap f (Pair a0 a1) = f a0 <> f a1

  foldl f b (Pair a0 a1) = (f (f b a0) a1)

  foldr f b (Pair a0 a1) = (f a0 (f a1 b))

instance foldableWithIndexPair :: FoldableWithIndex (Boolean) Pair where
  foldMapWithIndex f (Pair a0 a1) = f false a0 <> f true a1

  foldlWithIndex f b (Pair a0 a1) = (f true (f false b a0) a1)

  foldrWithIndex f b (Pair a0 a1) = (f false a0 (f true a1 b))

instance traversablePair :: Traversable Pair where
  traverse f (Pair a0 a1) = Pair <$> f a0 <*> f a1

  sequence (Pair a0 a1) = Pair <$> a0 <*> a1

instance traversableWithIndexPair :: TraversableWithIndex (Boolean) Pair where
  traverseWithIndex f (Pair a0 a1) = Pair <$> f false a0 <*> f true a1

data Pair' a = Pair0 {- a -} a | Pair1 a {- a -}
derive instance eqPair' :: Eq a => Eq (Pair' a)
derive instance ordPair' :: Ord a => Ord (Pair' a)
derive instance eq1Pair' :: Eq1 Pair'
derive instance ord1Pair' :: Ord1 Pair'

instance functorPair' :: Functor Pair' where
  map f (Pair0 a0) = Pair0 (f a0)
  map f (Pair1 a0) = Pair1 (f a0)

instance foldablePair' :: Foldable Pair' where
  foldMap f (Pair0 a0) = f a0
  foldMap f (Pair1 a0) = f a0

  foldl f b (Pair0 a0) = (f b a0)
  foldl f b (Pair1 a0) = (f b a0)

  foldr f b (Pair0 a0) = (f a0 b)
  foldr f b (Pair1 a0) = (f a0 b)

instance traversablePair' :: Traversable Pair' where
  traverse f (Pair0 a0) = Pair0 <$> f a0
  traverse f (Pair1 a0) = Pair1 <$> f a0

  sequence (Pair0 a0) = Pair0 <$> a0
  sequence (Pair1 a0) = Pair1 <$> a0

data Triplet a = Triplet a a a
derive instance eqTriplet :: Eq a => Eq (Triplet a)
derive instance ordTriplet :: Ord a => Ord (Triplet a)
derive instance eq1Triplet :: Eq1 Triplet
derive instance ord1Triplet :: Ord1 Triplet

instance functorTriplet :: Functor Triplet where
  map f (Triplet a0 a1 a2) = Triplet (f a0) (f a1) (f a2)

instance functorWithIndexTriplet :: FunctorWithIndex (Three) Triplet where
  mapWithIndex f (Triplet a0 a1 a2) = Triplet (f Three1 a0) (f Three2 a1) (f Three3 a2)

instance foldableTriplet :: Foldable Triplet where
  foldMap f (Triplet a0 a1 a2) = f a0 <> f a1 <> f a2

  foldl f b (Triplet a0 a1 a2) = (f (f (f b a0) a1) a2)

  foldr f b (Triplet a0 a1 a2) = (f a0 (f a1 (f a2 b)))

instance foldableWithIndexTriplet :: FoldableWithIndex (Three) Triplet where
  foldMapWithIndex f (Triplet a0 a1 a2) = f Three1 a0 <> f Three2 a1 <> f Three3 a2

  foldlWithIndex f b (Triplet a0 a1 a2) = (f Three3 (f Three2 (f Three1 b a0) a1) a2)

  foldrWithIndex f b (Triplet a0 a1 a2) = (f Three1 a0 (f Three2 a1 (f Three3 a2 b)))

instance traversableTriplet :: Traversable Triplet where
  traverse f (Triplet a0 a1 a2) = Triplet <$> f a0 <*> f a1 <*> f a2

  sequence (Triplet a0 a1 a2) = Triplet <$> a0 <*> a1 <*> a2

instance traversableWithIndexTriplet :: TraversableWithIndex (Three) Triplet where
  traverseWithIndex f (Triplet a0 a1 a2) = Triplet <$> f Three1 a0 <*> f Three2 a1 <*> f Three3 a2

data Triplet' a = Triplet0 {- a -} a a | Triplet1 a {- a -} a | Triplet2 a a {- a -}
derive instance eqTriplet' :: Eq a => Eq (Triplet' a)
derive instance ordTriplet' :: Ord a => Ord (Triplet' a)
derive instance eq1Triplet' :: Eq1 Triplet'
derive instance ord1Triplet' :: Ord1 Triplet'

instance functorTriplet' :: Functor Triplet' where
  map f (Triplet0 a0 a1) = Triplet0 (f a0) (f a1)
  map f (Triplet1 a0 a1) = Triplet1 (f a0) (f a1)
  map f (Triplet2 a0 a1) = Triplet2 (f a0) (f a1)

instance foldableTriplet' :: Foldable Triplet' where
  foldMap f (Triplet0 a0 a1) = f a0 <> f a1
  foldMap f (Triplet1 a0 a1) = f a0 <> f a1
  foldMap f (Triplet2 a0 a1) = f a0 <> f a1

  foldl f b (Triplet0 a0 a1) = (f (f b a0) a1)
  foldl f b (Triplet1 a0 a1) = (f (f b a0) a1)
  foldl f b (Triplet2 a0 a1) = (f (f b a0) a1)

  foldr f b (Triplet0 a0 a1) = (f a0 (f a1 b))
  foldr f b (Triplet1 a0 a1) = (f a0 (f a1 b))
  foldr f b (Triplet2 a0 a1) = (f a0 (f a1 b))

instance traversableTriplet' :: Traversable Triplet' where
  traverse f (Triplet0 a0 a1) = Triplet0 <$> f a0 <*> f a1
  traverse f (Triplet1 a0 a1) = Triplet1 <$> f a0 <*> f a1
  traverse f (Triplet2 a0 a1) = Triplet2 <$> f a0 <*> f a1

  sequence (Triplet0 a0 a1) = Triplet0 <$> a0 <*> a1
  sequence (Triplet1 a0 a1) = Triplet1 <$> a0 <*> a1
  sequence (Triplet2 a0 a1) = Triplet2 <$> a0 <*> a1

data TextLitF a = TextLit String | TextInterp String a (TextLitF a)
derive instance eqTextLitF :: Eq a => Eq (TextLitF a)
derive instance ordTextLitF :: Ord a => Ord (TextLitF a)
derive instance eq1TextLitF :: Eq1 TextLitF
derive instance ord1TextLitF :: Ord1 TextLitF

instance functorTextLitF :: Functor TextLitF where
  map f (TextLit s) = TextLit s
  map f (TextInterp s a0 a1) = TextInterp s (f a0) (map f a1)

instance functorWithIndexTextLitF :: FunctorWithIndex (Natural) TextLitF where
  mapWithIndex f (TextLit s) = TextLit s
  mapWithIndex f (TextInterp s a0 a1) = TextInterp s (f zero a0) (mapWithIndex (\i -> f (one + i)) a1)

instance foldableTextLitF :: Foldable TextLitF where
  foldMap f (TextLit _) = mempty
  foldMap f (TextInterp _ a0 a1) = f a0 <> foldMap f a1

  foldl f b (TextLit _) = b
  foldl f b (TextInterp _ a0 a1) = (foldl f (f b a0) a1)

  foldr f b (TextLit _) = b
  foldr f b (TextInterp _ a0 a1) = (f a0 (foldr f b a1))

instance foldableWithIndexTextLitF :: FoldableWithIndex (Natural) TextLitF where
  foldMapWithIndex f (TextLit _) = mempty
  foldMapWithIndex f (TextInterp _ a0 a1) = f zero a0 <> foldMapWithIndex (\i -> f (one + i)) a1

  foldlWithIndex f b (TextLit _) = b
  foldlWithIndex f b (TextInterp _ a0 a1) = (foldlWithIndex (\i -> f (one + i)) (f zero b a0) a1)

  foldrWithIndex f b (TextLit _) = b
  foldrWithIndex f b (TextInterp _ a0 a1) = (f zero a0 (foldrWithIndex (\i -> f (one + i)) b a1))

instance traversableTextLitF :: Traversable TextLitF where
  traverse f (TextLit s) = pure (TextLit s)
  traverse f (TextInterp s a0 a1) = TextInterp s <$> f a0 <*> traverse f a1

  sequence (TextLit s) = pure (TextLit s)
  sequence (TextInterp s a0 a1) = TextInterp s <$> a0 <*> sequence a1

instance traversableWithIndexTextLitF :: TraversableWithIndex (Natural) TextLitF where
  traverseWithIndex f (TextLit s) = pure (TextLit s)
  traverseWithIndex f (TextInterp s a0 a1) = TextInterp s <$> f zero a0 <*> traverseWithIndex (\i -> f (one + i)) a1

data TextLitF' a = TextInterp0 String {- a -} (TextLitF a) | TextInterp1 String a (TextLitF' a)
derive instance eqTextLitF' :: Eq a => Eq (TextLitF' a)
derive instance ordTextLitF' :: Ord a => Ord (TextLitF' a)
derive instance eq1TextLitF' :: Eq1 TextLitF'
derive instance ord1TextLitF' :: Ord1 TextLitF'

instance functorTextLitF' :: Functor TextLitF' where
  map f (TextInterp0 s a0) = TextInterp0 s (map f a0)
  map f (TextInterp1 s a0 a1) = TextInterp1 s (f a0) (map f a1)

instance foldableTextLitF' :: Foldable TextLitF' where
  foldMap f (TextInterp0 _ a0) = foldMap f a0
  foldMap f (TextInterp1 _ a0 a1) = f a0 <> foldMap f a1

  foldl f b (TextInterp0 _ a0) = (foldl f b a0)
  foldl f b (TextInterp1 _ a0 a1) = (foldl f (f b a0) a1)

  foldr f b (TextInterp0 _ a0) = (foldr f b a0)
  foldr f b (TextInterp1 _ a0 a1) = (f a0 (foldr f b a1))

instance traversableTextLitF' :: Traversable TextLitF' where
  traverse f (TextInterp0 s a0) = TextInterp0 s <$> traverse f a0
  traverse f (TextInterp1 s a0 a1) = TextInterp1 s <$> f a0 <*> traverse f a1

  sequence (TextInterp0 s a0) = TextInterp0 s <$> sequence a0
  sequence (TextInterp1 s a0 a1) = TextInterp1 s <$> a0 <*> sequence a1

data MergeF a = MergeF a a (Maybe a)
derive instance eqMergeF :: Eq a => Eq (MergeF a)
derive instance ordMergeF :: Ord a => Ord (MergeF a)
derive instance eq1MergeF :: Eq1 MergeF
derive instance ord1MergeF :: Ord1 MergeF

instance functorMergeF :: Functor MergeF where
  map f (MergeF a0 a1 a2) = MergeF (f a0) (f a1) (map f a2)

instance functorWithIndexMergeF :: FunctorWithIndex (Three) MergeF where
  mapWithIndex f (MergeF a0 a1 a2) = MergeF (f Three1 a0) (f Three2 a1) (mapWithIndex (\i -> f (const Three3 i)) a2)

instance foldableMergeF :: Foldable MergeF where
  foldMap f (MergeF a0 a1 a2) = f a0 <> f a1 <> foldMap f a2

  foldl f b (MergeF a0 a1 a2) = (foldl f (f (f b a0) a1) a2)

  foldr f b (MergeF a0 a1 a2) = (f a0 (f a1 (foldr f b a2)))

instance foldableWithIndexMergeF :: FoldableWithIndex (Three) MergeF where
  foldMapWithIndex f (MergeF a0 a1 a2) = f Three1 a0 <> f Three2 a1 <> foldMapWithIndex (\i -> f (const Three3 i)) a2

  foldlWithIndex f b (MergeF a0 a1 a2) = (foldlWithIndex (\i -> f (const Three3 i)) (f Three2 (f Three1 b a0) a1) a2)

  foldrWithIndex f b (MergeF a0 a1 a2) = (f Three1 a0 (f Three2 a1 (foldrWithIndex (\i -> f (const Three3 i)) b a2)))

instance traversableMergeF :: Traversable MergeF where
  traverse f (MergeF a0 a1 a2) = MergeF <$> f a0 <*> f a1 <*> traverse f a2

  sequence (MergeF a0 a1 a2) = MergeF <$> a0 <*> a1 <*> sequence a2

instance traversableWithIndexMergeF :: TraversableWithIndex (Three) MergeF where
  traverseWithIndex f (MergeF a0 a1 a2) = MergeF <$> f Three1 a0 <*> f Three2 a1 <*> traverseWithIndex (\i -> f (const Three3 i)) a2

data MergeF' a = MergeF0 {- a -} a (Maybe a) | MergeF1 a {- a -} (Maybe a) | MergeF2 a a (Maybe' a)
derive instance eqMergeF' :: Eq a => Eq (MergeF' a)
derive instance ordMergeF' :: Ord a => Ord (MergeF' a)
derive instance eq1MergeF' :: Eq1 MergeF'
derive instance ord1MergeF' :: Ord1 MergeF'

instance functorMergeF' :: Functor MergeF' where
  map f (MergeF0 a0 a1) = MergeF0 (f a0) (map f a1)
  map f (MergeF1 a0 a1) = MergeF1 (f a0) (map f a1)
  map f (MergeF2 a0 a1 a2) = MergeF2 (f a0) (f a1) (map f a2)

instance foldableMergeF' :: Foldable MergeF' where
  foldMap f (MergeF0 a0 a1) = f a0 <> foldMap f a1
  foldMap f (MergeF1 a0 a1) = f a0 <> foldMap f a1
  foldMap f (MergeF2 a0 a1 a2) = f a0 <> f a1 <> foldMap f a2

  foldl f b (MergeF0 a0 a1) = (foldl f (f b a0) a1)
  foldl f b (MergeF1 a0 a1) = (foldl f (f b a0) a1)
  foldl f b (MergeF2 a0 a1 a2) = (foldl f (f (f b a0) a1) a2)

  foldr f b (MergeF0 a0 a1) = (f a0 (foldr f b a1))
  foldr f b (MergeF1 a0 a1) = (f a0 (foldr f b a1))
  foldr f b (MergeF2 a0 a1 a2) = (f a0 (f a1 (foldr f b a2)))

instance traversableMergeF' :: Traversable MergeF' where
  traverse f (MergeF0 a0 a1) = MergeF0 <$> f a0 <*> traverse f a1
  traverse f (MergeF1 a0 a1) = MergeF1 <$> f a0 <*> traverse f a1
  traverse f (MergeF2 a0 a1 a2) = MergeF2 <$> f a0 <*> f a1 <*> traverse f a2

  sequence (MergeF0 a0 a1) = MergeF0 <$> a0 <*> sequence a1
  sequence (MergeF1 a0 a1) = MergeF1 <$> a0 <*> sequence a1
  sequence (MergeF2 a0 a1 a2) = MergeF2 <$> a0 <*> a1 <*> sequence a2

data LetF a = LetF String (Maybe a) a a
derive instance eqLetF :: Eq a => Eq (LetF a)
derive instance ordLetF :: Ord a => Ord (LetF a)
derive instance eq1LetF :: Eq1 LetF
derive instance ord1LetF :: Ord1 LetF

instance functorLetF :: Functor LetF where
  map f (LetF s a0 a1 a2) = LetF s (map f a0) (f a1) (f a2)

instance functorWithIndexLetF :: FunctorWithIndex (Three) LetF where
  mapWithIndex f (LetF s a0 a1 a2) = LetF s (mapWithIndex (\i -> f (const Three1 i)) a0) (f Three2 a1) (f Three3 a2)

instance foldableLetF :: Foldable LetF where
  foldMap f (LetF _ a0 a1 a2) = foldMap f a0 <> f a1 <> f a2

  foldl f b (LetF _ a0 a1 a2) = (f (f (foldl f b a0) a1) a2)

  foldr f b (LetF _ a0 a1 a2) = (foldr f (f a1 (f a2 b)) a0)

instance foldableWithIndexLetF :: FoldableWithIndex (Three) LetF where
  foldMapWithIndex f (LetF _ a0 a1 a2) = foldMapWithIndex (\i -> f (const Three1 i)) a0 <> f Three2 a1 <> f Three3 a2

  foldlWithIndex f b (LetF _ a0 a1 a2) = (f Three3 (f Three2 (foldlWithIndex (\i -> f (const Three1 i)) b a0) a1) a2)

  foldrWithIndex f b (LetF _ a0 a1 a2) = (foldrWithIndex (\i -> f (const Three1 i)) (f Three2 a1 (f Three3 a2 b)) a0)

instance traversableLetF :: Traversable LetF where
  traverse f (LetF s a0 a1 a2) = LetF s <$> traverse f a0 <*> f a1 <*> f a2

  sequence (LetF s a0 a1 a2) = LetF s <$> sequence a0 <*> a1 <*> a2

instance traversableWithIndexLetF :: TraversableWithIndex (Three) LetF where
  traverseWithIndex f (LetF s a0 a1 a2) = LetF s <$> traverseWithIndex (\i -> f (const Three1 i)) a0 <*> f Three2 a1 <*> f Three3 a2

data LetF' a = LetF0 String (Maybe' a) a a | LetF1 String (Maybe a) {- a -} a | LetF2 String (Maybe a) a {- a -}
derive instance eqLetF' :: Eq a => Eq (LetF' a)
derive instance ordLetF' :: Ord a => Ord (LetF' a)
derive instance eq1LetF' :: Eq1 LetF'
derive instance ord1LetF' :: Ord1 LetF'

instance functorLetF' :: Functor LetF' where
  map f (LetF0 s a0 a1 a2) = LetF0 s (map f a0) (f a1) (f a2)
  map f (LetF1 s a0 a1) = LetF1 s (map f a0) (f a1)
  map f (LetF2 s a0 a1) = LetF2 s (map f a0) (f a1)

instance foldableLetF' :: Foldable LetF' where
  foldMap f (LetF0 _ a0 a1 a2) = foldMap f a0 <> f a1 <> f a2
  foldMap f (LetF1 _ a0 a1) = foldMap f a0 <> f a1
  foldMap f (LetF2 _ a0 a1) = foldMap f a0 <> f a1

  foldl f b (LetF0 _ a0 a1 a2) = (f (f (foldl f b a0) a1) a2)
  foldl f b (LetF1 _ a0 a1) = (f (foldl f b a0) a1)
  foldl f b (LetF2 _ a0 a1) = (f (foldl f b a0) a1)

  foldr f b (LetF0 _ a0 a1 a2) = (foldr f (f a1 (f a2 b)) a0)
  foldr f b (LetF1 _ a0 a1) = (foldr f (f a1 b) a0)
  foldr f b (LetF2 _ a0 a1) = (foldr f (f a1 b) a0)

instance traversableLetF' :: Traversable LetF' where
  traverse f (LetF0 s a0 a1 a2) = LetF0 s <$> traverse f a0 <*> f a1 <*> f a2
  traverse f (LetF1 s a0 a1) = LetF1 s <$> traverse f a0 <*> f a1
  traverse f (LetF2 s a0 a1) = LetF2 s <$> traverse f a0 <*> f a1

  sequence (LetF0 s a0 a1 a2) = LetF0 s <$> sequence a0 <*> a1 <*> a2
  sequence (LetF1 s a0 a1) = LetF1 s <$> sequence a0 <*> a1
  sequence (LetF2 s a0 a1) = LetF2 s <$> sequence a0 <*> a1

data BindingBody a = BindingBody String a a
derive instance eqBindingBody :: Eq a => Eq (BindingBody a)
derive instance ordBindingBody :: Ord a => Ord (BindingBody a)
derive instance eq1BindingBody :: Eq1 BindingBody
derive instance ord1BindingBody :: Ord1 BindingBody

instance functorBindingBody :: Functor BindingBody where
  map f (BindingBody s a0 a1) = BindingBody s (f a0) (f a1)

instance functorWithIndexBindingBody :: FunctorWithIndex (Boolean) BindingBody where
  mapWithIndex f (BindingBody s a0 a1) = BindingBody s (f false a0) (f true a1)

instance foldableBindingBody :: Foldable BindingBody where
  foldMap f (BindingBody _ a0 a1) = f a0 <> f a1

  foldl f b (BindingBody _ a0 a1) = (f (f b a0) a1)

  foldr f b (BindingBody _ a0 a1) = (f a0 (f a1 b))

instance foldableWithIndexBindingBody :: FoldableWithIndex (Boolean) BindingBody where
  foldMapWithIndex f (BindingBody _ a0 a1) = f false a0 <> f true a1

  foldlWithIndex f b (BindingBody _ a0 a1) = (f true (f false b a0) a1)

  foldrWithIndex f b (BindingBody _ a0 a1) = (f false a0 (f true a1 b))

instance traversableBindingBody :: Traversable BindingBody where
  traverse f (BindingBody s a0 a1) = BindingBody s <$> f a0 <*> f a1

  sequence (BindingBody s a0 a1) = BindingBody s <$> a0 <*> a1

instance traversableWithIndexBindingBody :: TraversableWithIndex (Boolean) BindingBody where
  traverseWithIndex f (BindingBody s a0 a1) = BindingBody s <$> f false a0 <*> f true a1

data BindingBody' a = BindingBody0 String {- a -} a | BindingBody1 String a {- a -}
derive instance eqBindingBody' :: Eq a => Eq (BindingBody' a)
derive instance ordBindingBody' :: Ord a => Ord (BindingBody' a)
derive instance eq1BindingBody' :: Eq1 BindingBody'
derive instance ord1BindingBody' :: Ord1 BindingBody'

instance functorBindingBody' :: Functor BindingBody' where
  map f (BindingBody0 s a0) = BindingBody0 s (f a0)
  map f (BindingBody1 s a0) = BindingBody1 s (f a0)

instance foldableBindingBody' :: Foldable BindingBody' where
  foldMap f (BindingBody0 _ a0) = f a0
  foldMap f (BindingBody1 _ a0) = f a0

  foldl f b (BindingBody0 _ a0) = (f b a0)
  foldl f b (BindingBody1 _ a0) = (f b a0)

  foldr f b (BindingBody0 _ a0) = (f a0 b)
  foldr f b (BindingBody1 _ a0) = (f a0 b)

instance traversableBindingBody' :: Traversable BindingBody' where
  traverse f (BindingBody0 s a0) = BindingBody0 s <$> f a0
  traverse f (BindingBody1 s a0) = BindingBody1 s <$> f a0

  sequence (BindingBody0 s a0) = BindingBody0 s <$> a0
  sequence (BindingBody1 s a0) = BindingBody1 s <$> a0

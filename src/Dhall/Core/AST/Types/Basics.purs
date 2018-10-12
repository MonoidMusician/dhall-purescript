module Dhall.Core.AST.Types.Basics where

import Prelude

import Data.Const as ConstF
import Data.Foldable (class Foldable, foldMap, foldl, foldr, foldrDefault)
import Data.Functor.Product (Product)
import Data.Identity (Identity)
import Data.Maybe (Maybe)
import Data.Traversable (class Traversable, sequenceDefault, traverse)
import Data.Tuple (Tuple)
import Data.Variant.Internal (FProxy)

type CONST a = FProxy (ConstF.Const a)
type UNIT = CONST Unit

data TextLitF a = TextLit String | TextInterp String a (TextLitF a)
derive instance eqTextLitF :: Eq a => Eq (TextLitF a)
derive instance ordTextLitF :: Ord a => Ord (TextLitF a)
derive instance functorTextLitF :: Functor TextLitF
instance foldableTextLitF :: Foldable TextLitF where
  foldMap _ (TextLit _) = mempty
  foldMap f (TextInterp _ a tla) = f a <> foldMap f tla
  foldl _ b (TextLit _) = b
  foldl f b (TextInterp _ a tla) = foldl f (f b a) tla
  foldr f = foldrDefault f
instance traversableTextLitF :: Traversable TextLitF where
  traverse f (TextLit s) = pure (TextLit s)
  traverse f (TextInterp s a tla) =
    TextInterp s <$> f a <*> traverse f tla
  sequence = sequenceDefault

data MergeF a = MergeF a a (Maybe a)
derive instance eqMergeF :: Eq a => Eq (MergeF a)
derive instance ordMergeF :: Ord a => Ord (MergeF a)
instance foldableMergeF :: Foldable MergeF where
  foldMap f (MergeF a1 a2 ma) = f a1 <> f a2 <> foldMap f ma
  foldl f b (MergeF a1 a2 ma) = foldl f (f (f b a1) a2) ma
  foldr f b (MergeF a1 a2 ma) = f a1 (f a2 (foldr f b ma))
instance traversableMergeF :: Traversable MergeF where
  traverse f (MergeF a1 a2 ma) = MergeF <$> f a1 <*> f a2 <*> traverse f ma
  sequence = sequenceDefault
derive instance functorMergeF :: Functor MergeF
data Triplet a = Triplet a a a
derive instance eqTriplet :: Eq a => Eq (Triplet a)
derive instance ordTriplet :: Ord a => Ord (Triplet a)
derive instance functorTriplet :: Functor Triplet
instance foldableTriplet :: Foldable Triplet where
  foldMap f (Triplet a1 a2 a3) = f a1 <> f a2 <> f a3
  foldl f b (Triplet a1 a2 a3) = f (f (f b a1) a2) a3
  foldr f b (Triplet a1 a2 a3) = f a1 (f a2 (f a3 b))
instance traversableTriplet :: Traversable Triplet where
  traverse f (Triplet a1 a2 a3) = Triplet <$> f a1 <*> f a2 <*> f a3
  sequence = sequenceDefault

data LetF a = LetF String (Maybe a) a a
derive instance eqLetF :: Eq a => Eq (LetF a)
derive instance ordLetF :: Ord a => Ord (LetF a)
instance foldableLetF :: Foldable LetF where
  foldMap f (LetF _ ma a1 a2) = foldMap f ma <> f a1 <> f a2
  foldl f b (LetF _ ma a1 a2) = f (f (foldl f b ma) a1) a2
  foldr f b (LetF _ ma a1 a2) = foldr f (f a1 (f a2 b)) ma
instance traversableLetF :: Traversable LetF where
  traverse f (LetF s ma a1 a2) = LetF s <$> traverse f ma <*> f a1 <*> f a2
  sequence = sequenceDefault
derive instance functorLetF :: Functor LetF
data Pair a = Pair a a
derive instance eqPair :: Eq a => Eq (Pair a)
derive instance ordPair :: Ord a => Ord (Pair a)
derive instance functorPair :: Functor Pair
instance foldablePair :: Foldable Pair where
  foldMap f (Pair a1 a2) = f a1 <> f a2
  foldl f b (Pair a1 a2) = f (f b a1) a2
  foldr f b (Pair a1 a2) = f a1 (f a2 b)
instance traversablePair :: Traversable Pair where
  traverse f (Pair a1 a2) = Pair <$> f a1 <*> f a2
  sequence = sequenceDefault

type BindingBody = Product (Tuple String) Identity

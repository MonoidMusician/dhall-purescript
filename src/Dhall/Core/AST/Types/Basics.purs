module Dhall.Core.AST.Types.Basics where

import Prelude

import Data.Const as ConstF
import Data.Foldable (class Foldable, foldMap, foldl, foldr, foldrDefault)
import Data.FoldableWithIndex (class FoldableWithIndex)
import Data.FunctorWithIndex (class FunctorWithIndex)
import Data.Maybe (Maybe)
import Data.Natural (Natural)
import Data.Traversable (class Traversable, sequenceDefault, traverse)
import Data.TraversableWithIndex (class TraversableWithIndex)
import Data.Variant.Internal (FProxy)

type CONST a = FProxy (ConstF.Const a)
type UNIT = CONST Unit

data Three = Three1 | Three2 | Three3
derive instance eqThree :: Eq Three
derive instance ordThree :: Ord Three

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
instance functorIxPair :: FunctorWithIndex Boolean Pair where
  mapWithIndex f (Pair a1 a2) = Pair (f false a1) (f true a2)
instance foldableIxPair :: FoldableWithIndex Boolean Pair where
  foldMapWithIndex f (Pair a1 a2) = f false a1 <> f true a2
  foldlWithIndex f b (Pair a1 a2) = f true (f false b a1) a2
  foldrWithIndex f b (Pair a1 a2) = f false a1 (f true a2 b)
instance traversableIxPair :: TraversableWithIndex Boolean Pair where
  traverseWithIndex f (Pair a1 a2) = Pair <$> f false a1 <*> f true a2

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
instance functorIxTriplet :: FunctorWithIndex Three Triplet where
  mapWithIndex f (Triplet a1 a2 a3) = Triplet
    (f Three1 a1) (f Three2 a2) (f Three3 a3)
instance foldableIxTriplet :: FoldableWithIndex Three Triplet where
  foldMapWithIndex f (Triplet a1 a2 a3) =
    f Three1 a1 <> f Three2 a2 <> f Three3 a3
  foldlWithIndex f b (Triplet a1 a2 a3) =
    f Three3 (f Three2 (f Three1 b a1) a2) a3
  foldrWithIndex f b (Triplet a1 a2 a3) =
    f Three1 a1 (f Three2 a2 (f Three3 a3 b))
instance traversableIxTriplet :: TraversableWithIndex Three Triplet where
  traverseWithIndex f (Triplet a1 a2 a3) = Triplet
    <$> f Three1 a1 <*> f Three2 a2 <*> f Three3 a3

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
  traverse _ (TextLit s) = pure (TextLit s)
  traverse f (TextInterp s a tla) =
    TextInterp s <$> f a <*> traverse f tla
  sequence = sequenceDefault
instance functorIxTextLitF :: FunctorWithIndex Natural TextLitF where
  mapWithIndex f = go zero where
    go _ (TextLit s) = TextLit s
    go i (TextInterp s a tla) = TextInterp s (f i a) $ go (i+one) tla
instance foldableIxTextLitF :: FoldableWithIndex Natural TextLitF where
  foldMapWithIndex f = go zero where
    go _ (TextLit _) = mempty
    go i (TextInterp s a tla) = f i a <> go (i+one) tla
  foldrWithIndex f = flip (go zero) where
    go _ (TextLit _) = identity
    go i (TextInterp _ a tla) = f i a <<< go (i+one) tla
  foldlWithIndex f = flip (go zero) where
    go _ (TextLit _) = identity
    go i (TextInterp _ a tla) = flip (f i) a >>> go (i+one) tla
instance traversableIxTextLitF :: TraversableWithIndex Natural TextLitF where
  traverseWithIndex f = go zero where
    go _ (TextLit s) = pure (TextLit s)
    go i (TextInterp s a tla) = TextInterp s <$> f i a <*> go (i+one) tla

data MergeF a = MergeF a a (Maybe a)
derive instance eqMergeF :: Eq a => Eq (MergeF a)
derive instance ordMergeF :: Ord a => Ord (MergeF a)
derive instance functorMergeF :: Functor MergeF
instance foldableMergeF :: Foldable MergeF where
  foldMap f (MergeF a1 a2 ma) = f a1 <> f a2 <> foldMap f ma
  foldl f b (MergeF a1 a2 ma) = foldl f (f (f b a1) a2) ma
  foldr f b (MergeF a1 a2 ma) = f a1 (f a2 (foldr f b ma))
instance traversableMergeF :: Traversable MergeF where
  traverse f (MergeF a1 a2 ma) = MergeF <$> f a1 <*> f a2 <*> traverse f ma
  sequence = sequenceDefault
instance functorIxMergeF :: FunctorWithIndex Three MergeF where
  mapWithIndex f (MergeF a1 a2 ma) = MergeF
    (f Three1 a1) (f Three2 a2) (f Three3 <$> ma)
instance foldableIxMergeF :: FoldableWithIndex Three MergeF where
  foldMapWithIndex f (MergeF a1 a2 ma) =
    f Three1 a1 <> f Three2 a2 <> foldMap (f Three3) ma
  foldlWithIndex f b (MergeF a1 a2 ma) =
    foldl (f Three3) (f Three2 (f Three1 b a1) a2) ma
  foldrWithIndex f b (MergeF a1 a2 ma) =
    f Three1 a1 (f Three2 a2 (foldr (f Three3) b ma))
instance traversableIxMergeF :: TraversableWithIndex Three MergeF where
  traverseWithIndex f (MergeF a1 a2 ma) = MergeF
    <$> f Three1 a1 <*> f Three2 a2 <*> traverse (f Three3) ma

data LetF a = LetF String (Maybe a) a a
derive instance eqLetF :: Eq a => Eq (LetF a)
derive instance ordLetF :: Ord a => Ord (LetF a)
derive instance functorLetF :: Functor LetF
instance foldableLetF :: Foldable LetF where
  foldMap f (LetF _ ma a1 a2) = foldMap f ma <> f a1 <> f a2
  foldl f b (LetF _ ma a1 a2) = f (f (foldl f b ma) a1) a2
  foldr f b (LetF _ ma a1 a2) = foldr f (f a1 (f a2 b)) ma
instance traversableLetF :: Traversable LetF where
  traverse f (LetF s ma a1 a2) = LetF s <$> traverse f ma <*> f a1 <*> f a2
  sequence = sequenceDefault
instance functorIxLetF :: FunctorWithIndex Three LetF where
  mapWithIndex f (LetF s ma a1 a2) = LetF s
    (f Three1 <$> ma) (f Three2 a1) (f Three3 a2)
instance foldableIxLetF :: FoldableWithIndex Three LetF where
  foldMapWithIndex f (LetF _ ma a1 a2) =
    foldMap (f Three1) ma <> f Three2 a1 <> f Three3 a2
  foldlWithIndex f b (LetF _ ma a1 a2) =
    f Three3 (f Three2 (foldl (f Three1) b ma) a1) a2
  foldrWithIndex f b (LetF _ ma a1 a2) =
    foldr (f Three1) (f Three2 a1 (f Three3 a2 b)) ma
instance traversableIxLetF :: TraversableWithIndex Three LetF where
  traverseWithIndex f (LetF s ma a1 a2) = LetF s
    <$> traverse (f Three1) ma <*> f Three2 a1 <*> f Three3 a2

data BindingBody a = BindingBody String a a
derive instance eqBindingBody :: Eq a => Eq (BindingBody a)
derive instance ordBindingBody :: Ord a => Ord (BindingBody a)
derive instance functorBindingBody :: Functor BindingBody
instance foldableBindingBody :: Foldable BindingBody where
  foldMap f (BindingBody _ a1 a2) = f a1 <> f a2
  foldl f b (BindingBody _ a1 a2) = f (f b a1) a2
  foldr f b (BindingBody _ a1 a2) = f a1 (f a2 b)
instance traversableBindingBody :: Traversable BindingBody where
  traverse f (BindingBody s a1 a2) = BindingBody s <$> f a1 <*> f a2
  sequence = sequenceDefault
instance functorIxBindingBody :: FunctorWithIndex Boolean BindingBody where
  mapWithIndex f (BindingBody s a1 a2) = BindingBody s
    (f false a1) (f true a2)
instance foldableIxBindingBody :: FoldableWithIndex Boolean BindingBody where
  foldMapWithIndex f (BindingBody _ a1 a2) =
    f false a1 <> f true a2
  foldlWithIndex f b (BindingBody _ a1 a2) =
    f true (f false b a1) a2
  foldrWithIndex f b (BindingBody _ a1 a2) =
    f false a1 (f true a2 b)
instance traversableIxBindingBody :: TraversableWithIndex Boolean BindingBody where
  traverseWithIndex f (BindingBody s a1 a2) = BindingBody s
    <$> f false a1 <*> f true a2

module Dhall.Core.Types where

import Prelude

import Data.Bifoldable (class Bifoldable, bifoldMap, bifoldl, bifoldr, bifoldlDefault, bifoldrDefault)
import Data.Bifunctor (class Bifunctor, lmap, rmap)
import Data.Const as ConstF
import Data.Foldable (class Foldable, foldMap, foldl, foldr, foldrDefault)
import Data.Functor.Compose (Compose)
import Data.Functor.Mu (Mu(In), transMu)
import Data.Functor.Product (Product)
import Data.Functor.Variant (SProxy(..), VariantF)
import Data.Functor.Variant as VariantF
import Data.Identity (Identity)
import Data.Maybe (Maybe)
import Data.Newtype (class Newtype, over, unwrap, wrap)
import Data.Set (Set)
import Data.Traversable (class Traversable, sequenceDefault, traverse)
import Data.Tuple (Tuple, fst)
import Data.Variant (Variant)
import Data.Variant as Variant
import Data.Variant.Internal (FProxy)
import Type.Row (type (+))

type OrdMap k = Compose Array (Tuple k)

data Const = Type | Kind
derive instance eqConst :: Eq Const
derive instance ordConst :: Ord Const

data Var = V String Int
derive instance eqVar :: Eq Var
derive instance ordVar :: Ord Var

type Literals vs =
  ( "BoolLit" :: Boolean
  , "NaturalLit" :: Int
  , "IntegerLit" :: Int
  | vs
  )

data TextLitF a = TextLit String | TextInterp String a (TextLitF a)
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

type Literals2 v =
  ( "TextLit" :: FProxy TextLitF
  , "ListLit" :: FProxy (Product Maybe Array)
  , "OptionalLit" :: FProxy (Product Identity Maybe)
  , "RecordLit" :: FProxy (OrdMap String)
  , "UnionLit" :: FProxy (Product (Tuple String) (OrdMap String))
  | v
  )

type BuiltinTypes vs =
  ( "Bool" :: Unit
  , "Natural" :: Unit
  , "Integer" :: Unit
  , "Double" :: Unit
  , "Text" :: Unit
  , "List" :: Unit
  , "Optional" :: Unit
  | vs
  )

type BuiltinTypes2 v =
  ( "Record" :: FProxy (OrdMap String)
  , "Union" :: FProxy (OrdMap String)
  | v
  )

type BuiltinFuncs vs =
  ( "NaturalFold" :: Unit
  , "NaturalBuild" :: Unit
  , "NaturalIsZero" :: Unit
  , "NaturalEven" :: Unit
  , "NaturalOdd" :: Unit
  , "NaturalToInteger" :: Unit
  , "NaturalShow" :: Unit
  , "IntegerShow" :: Unit
  , "IntegerToDouble" :: Unit
  , "DoubleShow" :: Unit
  , "ListBuild" :: Unit
  , "ListFold" :: Unit
  , "ListLength" :: Unit
  , "ListHead" :: Unit
  , "ListLast" :: Unit
  , "ListIndexed" :: Unit
  , "ListReverse" :: Unit
  , "OptionalFold" :: Unit
  , "OptionalBuild" :: Unit
  | vs
  )

type BuiltinBinOps vs =
  ( "BoolAnd" :: Unit
  , "BoolOr" :: Unit
  , "BoolEQ" :: Unit
  , "BoolNE" :: Unit
  , "NaturalPlus" :: Unit
  , "NaturalTimes" :: Unit
  , "TextAppend" :: Unit
  , "ListAppend" :: Unit
  , "Combine" :: Unit
  , "CombineTypes" :: Unit
  , "Prefer" :: Unit
  , "ImportAlt" :: Unit
  | vs
  )

data BinOpF v a = BinOpF (Variant v) a a
derive instance functorBinOpF :: Functor (BinOpF v)
instance foldableBinOpF :: Foldable (BinOpF v) where
  foldMap f (BinOpF _ a1 a2) = f a1 <> f a2
  foldl f b (BinOpF _ a1 a2) = f (f b a1) a2
  foldr f b (BinOpF _ a1 a2) = f a1 (f a2 b)
instance traversableBinOpF :: Traversable (BinOpF v) where
  traverse f (BinOpF v a1 a2) = BinOpF v <$> f a1 <*> f a2
  sequence = sequenceDefault
data MergeF a = MergeF a a (Maybe a)
instance foldableMergeF :: Foldable MergeF where
  foldMap f (MergeF a1 a2 ma) = f a1 <> f a2 <> foldMap f ma
  foldl f b (MergeF a1 a2 ma) = foldl f (f (f b a1) a2) ma
  foldr f b (MergeF a1 a2 ma) = f a1 (f a2 (foldr f b ma))
instance traversableMergeF :: Traversable MergeF where
  traverse f (MergeF a1 a2 ma) = MergeF <$> f a1 <*> f a2 <*> traverse f ma
  sequence = sequenceDefault
derive instance functorMergeF :: Functor MergeF
data Triplet a = Triplet a a a
derive instance functorTriplet :: Functor Triplet
instance foldableTriplet :: Foldable Triplet where
  foldMap f (Triplet a1 a2 a3) = f a1 <> f a2 <> f a3
  foldl f b (Triplet a1 a2 a3) = f (f (f b a1) a2) a3
  foldr f b (Triplet a1 a2 a3) = f a1 (f a2 (f a3 b))
instance traversableTriplet :: Traversable Triplet where
  traverse f (Triplet a1 a2 a3) = Triplet <$> f a1 <*> f a2 <*> f a3
  sequence = sequenceDefault

type BuiltinOps v =
  ( "BinOp" :: FProxy (BinOpF (BuiltinBinOps ()))
  , "BoolIf" :: FProxy (Triplet)
  , "Field" :: FProxy (Tuple String)
  , "Project" :: FProxy (Tuple (Set String))
  , "Merge" :: FProxy (MergeF)
  | v
  )

type Terminals vs =
  ( "Const" :: Const
  , "Var" :: Var
  | vs
  )

data LetF a = LetF String (Maybe a) a a
instance foldableLetF :: Foldable LetF where
  foldMap f (LetF _ ma a1 a2) = foldMap f ma <> f a1 <> f a2
  foldl f b (LetF _ ma a1 a2) = f (f (foldl f b ma) a1) a2
  foldr f b (LetF _ ma a1 a2) = foldr f (f a1 (f a2 b)) ma
instance traversableLetF :: Traversable LetF where
  traverse f (LetF s ma a1 a2) = LetF s <$> traverse f ma <*> f a1 <*> f a2
  sequence = sequenceDefault
derive instance functorLetF :: Functor LetF
data Pair a = Pair a a
derive instance functorPair :: Functor Pair
instance foldablePair :: Foldable Pair where
  foldMap f (Pair a1 a2) = f a1 <> f a2
  foldl f b (Pair a1 a2) = f (f b a1) a2
  foldr f b (Pair a1 a2) = f a1 (f a2 b)
instance traversablePair :: Traversable Pair where
  traverse f (Pair a1 a2) = Pair <$> f a1 <*> f a2
  sequence = sequenceDefault

type Syntax v =
  ( "Lam" :: FProxy (Product (Tuple String) Identity)
  , "Pi" :: FProxy (Product (Tuple String) Identity)
  , "App" :: FProxy (Pair)
  , "Let" :: FProxy LetF
  , "Annot" :: FProxy (Pair)
  | v
  )

type SimpleThings vs = Literals + BuiltinTypes + BuiltinFuncs + Terminals + vs

type FunctorThings v = Literals2 + BuiltinTypes2 + BuiltinOps + Syntax + v

type AllTheThings vs v =
  ( "SimpleThings" :: FProxy (ConstF.Const (Variant (SimpleThings + vs)))
  | FunctorThings + v
  )

newtype Expr s a = Expr (Mu (VariantF (
  AllTheThings
    ( "Embed" :: a )
    ( "Note" :: FProxy (Tuple s) )
  )))
derive instance newtypeExpr :: Newtype (Expr s a) _

instance bifunctorExpr :: Bifunctor Expr where
  bimap f g (Expr e) = Expr $ e # transMu
    ( VariantF.expand
    # VariantF.on (SProxy :: SProxy "SimpleThings")
      ( compose (VariantF.inj (SProxy :: SProxy "SimpleThings"))
      $ over ConstF.Const
      $ Variant.expand
      # Variant.on (SProxy :: SProxy "Embed")
        (g >>> Variant.inj (SProxy :: SProxy "Embed"))
      )
    # VariantF.on (SProxy :: SProxy "Note")
      (lmap f >>> VariantF.inj (SProxy :: SProxy "Note"))
    )
instance functorExpr :: Functor (Expr s) where
  map = rmap
instance applyExpr :: Apply (Expr s) where
  apply = ap
instance applicativeExpr :: Applicative (Expr s) where
  pure a = wrap $ wrap $
    VariantF.inj (SProxy :: SProxy "SimpleThings") $
      wrap $ Variant.inj (SProxy :: SProxy "Embed") a
instance bindExpr :: Bind (Expr s) where
  bind (Expr (In e)) k = Expr $ In $ e #
    ( (VariantF.expand >>> map (\i -> unwrap ((Expr i) >>= k)))
    # VariantF.on (SProxy :: SProxy "SimpleThings")
      ( (>>>) unwrap $
      ( Variant.expand >>> ConstF.Const >>> VariantF.inj (SProxy :: SProxy "SimpleThings"))
      # Variant.on (SProxy :: SProxy "Embed") (k >>> unwrap >>> unwrap)
      )
    )
instance monadExpr :: Monad (Expr s)

instance bifoldableExpr :: Bifoldable Expr where
  bifoldMap f g (Expr (In e)) =
    ( foldMap (Expr >>> bifoldMap f g)
    # VariantF.on (SProxy :: SProxy "SimpleThings")
      ( (>>>) (unwrap)
      $ mempty
      # Variant.on (SProxy :: SProxy "Embed") g
      )
    # VariantF.on (SProxy :: SProxy "Note") (fst >>> f)
    ) e
  bifoldr f g = bifoldrDefault f g
  bifoldl f g = bifoldlDefault f g
instance foldableExpr :: Foldable (Expr s) where
  foldMap = bifoldMap mempty
  foldl = bifoldl const
  foldr = bifoldr (const identity)

module Dhall.Core.Types where

import Prelude

import Data.Bifoldable (class Bifoldable, bifoldMap, bifoldl, bifoldr)
import Data.Bifunctor (class Bifunctor, lmap, rmap)
import Data.Const as ConstF
import Data.Foldable (class Foldable, foldMap, foldl, foldr, foldrDefault)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Mu (Mu(In), transMu)
import Data.Functor.Product (Product, product)
import Data.Functor.Variant (VariantF)
import Data.Functor.Variant as VariantF
import Data.Identity (Identity(..))
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, over, unwrap)
import Data.Set (Set)
import Data.Symbol (class IsSymbol, SProxy(..))
import Data.Traversable (class Traversable, sequenceDefault, traverse)
import Data.Tuple (Tuple(..))
import Data.Variant (Variant)
import Data.Variant as Variant
import Data.Variant.Internal (FProxy)
import Type.Row (type (+))
import Data.Lens (Prism', prism', Iso', iso, view, review, re)
import Data.Lens.Iso.Newtype (_Newtype)
import Prim.Row as Row

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
  , "DoubleLit" :: Number
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
  , "Constructors" :: FProxy Identity
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

type ExprRow s a =
  AllTheThings
    ( "Embed" :: a )
    ( "Note" :: FProxy (Tuple s) )

newtype Expr s a = Expr (Mu (VariantF (ExprRow s a)))
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
  pure = mkEmbed
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
    # VariantF.on (SProxy :: SProxy "Note")
      (\(Tuple s rest) -> f s <> bifoldMap f g (Expr rest))
    ) e
  bifoldr f g c (Expr (In e)) =
    ( foldr (\i a -> bifoldr f g a (Expr i)) c
    # VariantF.on (SProxy :: SProxy "SimpleThings")
      ( (>>>) (unwrap)
      $ Variant.default c
      # Variant.on (SProxy :: SProxy "Embed") (g <@> c)
      )
    # VariantF.on (SProxy :: SProxy "Note")
      (\(Tuple a rest) -> f a (bifoldr f g c (Expr rest)))
    ) e
  bifoldl f g c (Expr (In e)) =
    ( foldl (\a i -> bifoldl f g a (Expr i)) c
    # VariantF.on (SProxy :: SProxy "SimpleThings")
      ( (>>>) (unwrap)
      $ Variant.default c
      # Variant.on (SProxy :: SProxy "Embed") (g c)
      )
    # VariantF.on (SProxy :: SProxy "Note")
      (\(Tuple a rest) -> bifoldl f g (f c a) (Expr rest))
    ) e
instance foldableExpr :: Foldable (Expr s) where
  foldMap = bifoldMap mempty
  foldl = bifoldl const
  foldr = bifoldr (const identity)

-- Pris(o)ms of the behemoth
_ExprF :: forall a s unused f k.
  Row.Cons k (FProxy f) unused (ExprRow s a) =>
  IsSymbol k => Functor f =>
  SProxy k -> Prism' (Expr s a) (f (Expr s a))
_ExprF k = _Newtype <<< _Newtype <<< mapIso (re _Newtype) <<< prism'
  (VariantF.inj k) (VariantF.default Nothing # VariantF.on k Just) where
    mapIso :: forall b c g. Functor g => Iso' b c -> Iso' (g b) (g c)
    mapIso i = iso (map (view i)) (map (review i))

_Expr :: forall a s unused v k.
  Row.Cons k v unused (SimpleThings ( "Embed" :: a )) =>
  IsSymbol k =>
  SProxy k -> Prism' (Expr s a) v
_Expr k = _ExprF (SProxy :: SProxy "SimpleThings") <<< _Newtype <<< prism'
  (Variant.inj k) (Variant.default Nothing # Variant.on k Just)

mkExprF :: forall a s unused f k.
  Row.Cons k (FProxy f) unused (ExprRow s a) =>
  IsSymbol k => Functor f =>
  SProxy k -> f (Expr s a) -> Expr s a
mkExprF k v = Expr (In (VariantF.inj k (unwrap <$> v)))

mkExpr :: forall a s unused v k.
  Row.Cons k v unused (SimpleThings ( "Embed" :: a )) =>
  IsSymbol k =>
  SProxy k -> v -> Expr s a
mkExpr k v = mkExprF (SProxy :: SProxy "SimpleThings")
  (ConstF.Const (Variant.inj k v))

mkBinOp :: forall a s unused k.
  Row.Cons k Unit unused (BuiltinBinOps ()) =>
  IsSymbol k =>
  SProxy k -> Expr s a -> Expr s a -> Expr s a
mkBinOp k l r = mkExprF (SProxy :: SProxy "BinOp")
  (BinOpF (Variant.inj k unit) l r)

mkConst :: forall s a. Const -> Expr s a
mkConst = mkExpr (SProxy :: SProxy "Const")

mkVar :: forall s a. Var -> Expr s a
mkVar = mkExpr (SProxy :: SProxy "Var")

mkLam :: forall s a. String -> Expr s a -> Expr s a -> Expr s a
mkLam name ty expr = mkExprF (SProxy :: SProxy "Lam")
  (product (Tuple name ty) (Identity expr))

mkPi :: forall s a. String -> Expr s a -> Expr s a -> Expr s a
mkPi name ty expr = mkExprF (SProxy :: SProxy "Pi")
  (product (Tuple name ty) (Identity expr))

mkApp :: forall s a. Expr s a -> Expr s a -> Expr s a
mkApp fn arg = mkExprF (SProxy :: SProxy "App")
  (Pair fn arg)

mkLet :: forall s a. String -> Maybe (Expr s a) -> Expr s a -> Expr s a -> Expr s a
mkLet name ty val expr = mkExprF (SProxy :: SProxy "Let")
  (LetF name ty val expr)

mkAnnot :: forall s a. Expr s a -> Expr s a -> Expr s a
mkAnnot val ty = mkExprF (SProxy :: SProxy "Annot")
  (Pair val ty)

mkBool :: forall s a. Expr s a
mkBool = mkExpr (SProxy :: SProxy "Bool") unit

mkBoolLit :: forall s a. Boolean -> Expr s a
mkBoolLit = mkExpr (SProxy :: SProxy "BoolLit")

mkBoolAnd :: forall s a. Expr s a -> Expr s a -> Expr s a
mkBoolAnd = mkBinOp (SProxy :: SProxy "BoolAnd")

mkBoolOr :: forall s a. Expr s a -> Expr s a -> Expr s a
mkBoolOr = mkBinOp (SProxy :: SProxy "BoolOr")

mkBoolEQ :: forall s a. Expr s a -> Expr s a -> Expr s a
mkBoolEQ = mkBinOp (SProxy :: SProxy "BoolEQ")

mkBoolNE :: forall s a. Expr s a -> Expr s a -> Expr s a
mkBoolNE = mkBinOp (SProxy :: SProxy "BoolNE")

mkBoolIf :: forall s a. Expr s a -> Expr s a -> Expr s a -> Expr s a
mkBoolIf cond t f = mkExprF (SProxy :: SProxy "BoolIf")
  (Triplet cond t f)

mkNatural :: forall s a. Expr s a
mkNatural = mkExpr (SProxy :: SProxy "Natural") unit

mkNaturalLit :: forall s a. Int -> Expr s a
mkNaturalLit = mkExpr (SProxy :: SProxy "NaturalLit")

mkNaturalFold :: forall s a. Expr s a
mkNaturalFold = mkExpr (SProxy :: SProxy "NaturalFold") unit

mkNaturalBuild :: forall s a. Expr s a
mkNaturalBuild = mkExpr (SProxy :: SProxy "NaturalBuild") unit

mkNaturalIsZero :: forall s a. Expr s a
mkNaturalIsZero = mkExpr (SProxy :: SProxy "NaturalIsZero") unit

mkNaturalEven :: forall s a. Expr s a
mkNaturalEven = mkExpr (SProxy :: SProxy "NaturalEven") unit

mkNaturalOdd :: forall s a. Expr s a
mkNaturalOdd = mkExpr (SProxy :: SProxy "NaturalOdd") unit

mkNaturalToInteger :: forall s a. Expr s a
mkNaturalToInteger = mkExpr (SProxy :: SProxy "NaturalToInteger") unit

mkNaturalShow :: forall s a. Expr s a
mkNaturalShow = mkExpr (SProxy :: SProxy "NaturalShow") unit

mkNaturalPlus :: forall s a. Expr s a -> Expr s a -> Expr s a
mkNaturalPlus = mkBinOp (SProxy :: SProxy "NaturalPlus")

mkNaturalTimes :: forall s a. Expr s a -> Expr s a -> Expr s a
mkNaturalTimes = mkBinOp (SProxy :: SProxy "NaturalTimes")

mkInteger :: forall s a. Expr s a
mkInteger = mkExpr (SProxy :: SProxy "Integer") unit

mkIntegerLit :: forall s a. Int -> Expr s a
mkIntegerLit = mkExpr (SProxy :: SProxy "IntegerLit")

mkIntegerShow :: forall s a. Expr s a
mkIntegerShow = mkExpr (SProxy :: SProxy "IntegerShow") unit

mkIntegerToDouble :: forall s a. Expr s a
mkIntegerToDouble = mkExpr (SProxy :: SProxy "IntegerToDouble") unit

mkDouble :: forall s a. Expr s a
mkDouble = mkExpr (SProxy :: SProxy "Double") unit

mkDoubleLit :: forall s a. Number -> Expr s a
mkDoubleLit = mkExpr (SProxy :: SProxy "DoubleLit")

mkDoubleShow :: forall s a. Expr s a
mkDoubleShow = mkExpr (SProxy :: SProxy "DoubleShow") unit

mkText :: forall s a. Expr s a
mkText = mkExpr (SProxy :: SProxy "Text") unit

mkTextLit :: forall s a. TextLitF (Expr s a) -> Expr s a
mkTextLit = mkExprF (SProxy :: SProxy "TextLit")

mkTextAppend :: forall s a. Expr s a -> Expr s a -> Expr s a
mkTextAppend = mkBinOp (SProxy :: SProxy "TextAppend")

mkList :: forall s a. Expr s a
mkList = mkExpr (SProxy :: SProxy "List") unit

mkListLit :: forall s a. Maybe (Expr s a) -> Array (Expr s a) -> Expr s a
mkListLit ty lit = mkExprF (SProxy :: SProxy "ListLit")
  (product ty lit)

mkListAppend :: forall s a. Expr s a -> Expr s a -> Expr s a
mkListAppend = mkBinOp (SProxy :: SProxy "ListAppend")

mkListFold :: forall s a. Expr s a
mkListFold = mkExpr (SProxy :: SProxy "ListFold") unit

mkListBuild :: forall s a. Expr s a
mkListBuild = mkExpr (SProxy :: SProxy "ListBuild") unit

mkListLength :: forall s a. Expr s a
mkListLength = mkExpr (SProxy :: SProxy "ListLength") unit

mkListHead :: forall s a. Expr s a
mkListHead = mkExpr (SProxy :: SProxy "ListHead") unit

mkListLast :: forall s a. Expr s a
mkListLast = mkExpr (SProxy :: SProxy "ListLast") unit

mkListIndexed :: forall s a. Expr s a
mkListIndexed = mkExpr (SProxy :: SProxy "ListIndexed") unit

mkListReverse :: forall s a. Expr s a
mkListReverse = mkExpr (SProxy :: SProxy "ListReverse") unit

mkOptional :: forall s a. Expr s a
mkOptional = mkExpr (SProxy :: SProxy "Optional") unit

mkOptionalLit :: forall s a. Expr s a -> Maybe (Expr s a) -> Expr s a
mkOptionalLit ty lit = mkExprF (SProxy :: SProxy "OptionalLit")
  (product (Identity ty) lit)

mkOptionalFold :: forall s a. Expr s a
mkOptionalFold = mkExpr (SProxy :: SProxy "OptionalFold") unit

mkOptionalBuild :: forall s a. Expr s a
mkOptionalBuild = mkExpr (SProxy :: SProxy "OptionalBuild") unit

mkRecord :: forall s a. Array (Tuple String (Expr s a)) -> Expr s a
mkRecord = mkExprF (SProxy :: SProxy "Record") <<< Compose

mkRecordLit :: forall s a. Array (Tuple String (Expr s a)) -> Expr s a
mkRecordLit = mkExprF (SProxy :: SProxy "RecordLit") <<< Compose

mkUnion :: forall s a. Array (Tuple String (Expr s a)) -> Expr s a
mkUnion = mkExprF (SProxy :: SProxy "Union") <<< Compose

mkUnionLit :: forall s a. String -> Expr s a -> Array (Tuple String (Expr s a)) -> Expr s a
mkUnionLit name ty others = mkExprF (SProxy :: SProxy "UnionLit")
  (product (Tuple name ty) (Compose others))

mkCombine :: forall s a. Expr s a -> Expr s a -> Expr s a
mkCombine = mkBinOp (SProxy :: SProxy "Combine")

mkCombineTypes :: forall s a. Expr s a -> Expr s a -> Expr s a
mkCombineTypes = mkBinOp (SProxy :: SProxy "CombineTypes")

mkPrefer :: forall s a. Expr s a -> Expr s a -> Expr s a
mkPrefer = mkBinOp (SProxy :: SProxy "Prefer")

mkMerge :: forall s a. Expr s a -> Expr s a -> Maybe (Expr s a) -> Expr s a
mkMerge x y t = mkExprF (SProxy :: SProxy "Merge")
  (MergeF x y t)

mkConstructors :: forall s a. Expr s a -> Expr s a
mkConstructors = mkExprF (SProxy :: SProxy "Constructors") <<< Identity

mkField :: forall s a. Expr s a -> String -> Expr s a
mkField expr field = mkExprF (SProxy :: SProxy "Field")
  (Tuple field expr)

mkProject :: forall s a. Expr s a -> Set String -> Expr s a
mkProject expr fields = mkExprF (SProxy :: SProxy "Project")
  (Tuple fields expr)

mkNote :: forall s a. s -> Expr s a -> Expr s a
mkNote note expr = mkExprF (SProxy :: SProxy "Note")
  (Tuple note expr)

mkImportAlt :: forall s a. Expr s a -> Expr s a -> Expr s a
mkImportAlt = mkBinOp (SProxy :: SProxy "ImportAlt")

mkEmbed :: forall s a. a -> Expr s a
mkEmbed = mkExpr (SProxy :: SProxy "Embed")

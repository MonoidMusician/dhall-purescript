module Dhall.Core.AST where

import Prelude

import Data.Bifoldable (class Bifoldable, bifoldMap, bifoldl, bifoldr)
import Data.Bifunctor (class Bifunctor, lmap, rmap)
import Data.Bitraversable (class Bitraversable, bitraverse, bisequenceDefault)
import Data.Const as ConstF
import Data.Eq (class Eq1)
import Data.Foldable (class Foldable, foldMap, foldl, foldr, foldrDefault)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Mu (Mu(In), roll, transMu, unroll)
import Data.Functor.Product (Product(..), product)
import Data.Functor.Variant (VariantF)
import Data.Functor.Variant as VariantF
import Data.Identity (Identity(..))
import Data.Lens (Prism', prism', Iso', iso, view, review, re, only)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, over, unwrap)
import Data.Set (Set)
import Data.String (joinWith)
import Data.Symbol (class IsSymbol, SProxy(..))
import Data.Traversable (class Traversable, sequenceDefault, traverse)
import Data.Tuple (Tuple(..), uncurry, swap)
import Data.Variant (Variant)
import Data.Variant as Variant
import Data.Variant.Internal (FProxy)
import Prim.Row as Row
import Type.Row (type (+))
import Matryoshka (cata)
import Unsafe.Coerce (unsafeCoerce)

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
derive instance eqBinOpF :: (Eq (Variant v), Eq a) => Eq (BinOpF v a)
derive instance functorBinOpF :: Functor (BinOpF v)
instance foldableBinOpF :: Foldable (BinOpF v) where
  foldMap f (BinOpF _ a1 a2) = f a1 <> f a2
  foldl f b (BinOpF _ a1 a2) = f (f b a1) a2
  foldr f b (BinOpF _ a1 a2) = f a1 (f a2 b)
instance traversableBinOpF :: Traversable (BinOpF v) where
  traverse f (BinOpF v a1 a2) = BinOpF v <$> f a1 <*> f a2
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

type Syntax v =
  ( "Lam" :: FProxy (BindingBody)
  , "Pi" :: FProxy (BindingBody)
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

instance showExpr :: (Show s, Show a) => Show (Expr s a) where
  show (Expr e0) = cata show1 e0 where
    lits e = "[" <> joinWith ", " e <> "]"
    rec e = lits $ e <#> \(Tuple k v) -> "(Tuple " <> show k <> v <> ")"
    mb =
      case _ of
        Nothing -> "(Nothing)"
        Just s -> "(Just " <> s <> ")"
    show1 =
      ( VariantF.case_
      # VariantF.on (SProxy :: SProxy "Annot")
        (\(Pair l r) -> "(mkAnnot " <> l <> r <> ")")
      # VariantF.on (SProxy :: SProxy "App")
        (\(Pair l r) -> "(mkApp " <> l <> r <> ")")
      # VariantF.on (SProxy :: SProxy "BinOp")
        (\(BinOpF v l r) ->
          let
            tag
              = Variant.case_
              # Variant.on (SProxy :: SProxy "BoolAnd") (const "BoolAnd")
              # Variant.on (SProxy :: SProxy "BoolOr") (const "BoolOr")
              # Variant.on (SProxy :: SProxy "BoolEQ") (const "BoolEQ")
              # Variant.on (SProxy :: SProxy "BoolNE") (const "BoolNE")
              # Variant.on (SProxy :: SProxy "NaturalPlus") (const "NaturalPlus")
              # Variant.on (SProxy :: SProxy "NaturalTimes") (const "NaturalTimes")
              # Variant.on (SProxy :: SProxy "TextAppend") (const "TextAppend")
              # Variant.on (SProxy :: SProxy "ListAppend") (const "ListAppend")
              # Variant.on (SProxy :: SProxy "Combine") (const "Combine")
              # Variant.on (SProxy :: SProxy "CombineTypes") (const "CombineTypes")
              # Variant.on (SProxy :: SProxy "Prefer") (const "Prefer")
              # Variant.on (SProxy :: SProxy "ImportAlt") (const "ImportAlt")
          in "(mk" <> tag v <> " " <> l <> r <> ")"
        )
      # VariantF.on (SProxy :: SProxy "BoolIf")
        (\(Triplet c t f) -> "(mkBoolIf " <> c <> t <> f <> ")")
      # VariantF.on (SProxy :: SProxy "Constructors")
        (\(Identity ty) -> "(mkConstructors " <> ty <> ")")
      # VariantF.on (SProxy :: SProxy "Field")
        (\(Tuple field e) -> "(mkField " <> e <> show field <> ")")
      # VariantF.on (SProxy :: SProxy "Lam")
        (\(Product (Tuple (Tuple n t) (Identity b))) -> "(mkLam " <> show n <> t <> b <> ")")
      # VariantF.on (SProxy :: SProxy "Let")
        (\(LetF n t e b) -> "(mkLet " <> n <> mb t <> e <> b <> ")")
      # VariantF.on (SProxy :: SProxy "ListLit")
        (\(Product (Tuple ty lit)) -> "(mkListLit " <> mb ty <> lits lit <> ")")
      # VariantF.on (SProxy :: SProxy "Merge")
        (\(MergeF a b c) -> "(mkMerge " <> a <> b <> mb c <> ")")
      # VariantF.on (SProxy :: SProxy "Note")
        (\(Tuple a b) -> "(mkNote (" <> show a <> ") " <> b <> ")")
      # VariantF.on (SProxy :: SProxy "OptionalLit")
        (\(Product (Tuple (Identity ty) lit)) -> "(mkOptionalLit " <> ty <> mb lit <> ")")
      # VariantF.on (SProxy :: SProxy "Pi")
        (\(Product (Tuple (Tuple n t) (Identity b))) -> "(mkPi " <> n <> t <> b <> ")")
      # VariantF.on (SProxy :: SProxy "Project")
        (\(Tuple projs e) -> "(mkProject " <> e <> show projs <> ")")
      # VariantF.on (SProxy :: SProxy "Record")
        (\(Compose a) -> "(mkRecord " <> rec a <> ")")
      # VariantF.on (SProxy :: SProxy "RecordLit")
        (\(Compose a) -> "(mkRecord " <> rec a <> ")")
      # VariantF.on (SProxy :: SProxy "SimpleThings")
        ( (>>>) unwrap
        $ Variant.case_
        # Variant.on (SProxy :: SProxy "BoolLit")
          (\b -> "(mkBoolLit " <> show b <> ")")
        # Variant.on (SProxy :: SProxy "NaturalLit")
          (\b -> "(mkNaturalLit " <> show b <> ")")
        # Variant.on (SProxy :: SProxy "IntegerLit")
          (\b -> "(mkIntegerLit " <> show b <> ")")
        # Variant.on (SProxy :: SProxy "DoubleLit")
          (\b -> "(mkDoubleLit " <> show b <> ")")
        # Variant.on (SProxy :: SProxy "Bool") (const "mkBool")
        # Variant.on (SProxy :: SProxy "Natural") (const "mkNatural")
        # Variant.on (SProxy :: SProxy "Integer") (const "mkInteger")
        # Variant.on (SProxy :: SProxy "Double") (const "mkDouble")
        # Variant.on (SProxy :: SProxy "Text") (const "mkText")
        # Variant.on (SProxy :: SProxy "List") (const "mkList")
        # Variant.on (SProxy :: SProxy "Optional") (const "mkOptional")
        # Variant.on (SProxy :: SProxy "NaturalFold") (const "mkNaturalFold")
        # Variant.on (SProxy :: SProxy "NaturalBuild") (const "mkNaturalBuild")
        # Variant.on (SProxy :: SProxy "NaturalIsZero") (const "mkNaturalIsZero")
        # Variant.on (SProxy :: SProxy "NaturalEven") (const "mkNaturalEven")
        # Variant.on (SProxy :: SProxy "NaturalOdd") (const "mkNaturalOdd")
        # Variant.on (SProxy :: SProxy "NaturalToInteger") (const "mkNaturalToInteger")
        # Variant.on (SProxy :: SProxy "NaturalShow") (const "mkNaturalShow")
        # Variant.on (SProxy :: SProxy "IntegerShow") (const "mkIntegerShow")
        # Variant.on (SProxy :: SProxy "IntegerToDouble") (const "mkIntegerToDouble")
        # Variant.on (SProxy :: SProxy "DoubleShow") (const "mkDoubleShow")
        # Variant.on (SProxy :: SProxy "ListBuild") (const "mkListBuild")
        # Variant.on (SProxy :: SProxy "ListFold") (const "mkListFold")
        # Variant.on (SProxy :: SProxy "ListLength") (const "mkListLength")
        # Variant.on (SProxy :: SProxy "ListHead") (const "mkListHead")
        # Variant.on (SProxy :: SProxy "ListLast") (const "mkListLast")
        # Variant.on (SProxy :: SProxy "ListIndexed") (const "mkListIndexed")
        # Variant.on (SProxy :: SProxy "ListReverse") (const "mkListReverse")
        # Variant.on (SProxy :: SProxy "OptionalFold") (const "mkOptionalFold")
        # Variant.on (SProxy :: SProxy "OptionalBuild") (const "mkOptionalBuild")
        # Variant.on (SProxy :: SProxy "Const")
            case _ of
              Type -> "(mkConst Type)"
              Kind -> "(mkConst Kind)"
        # Variant.on (SProxy :: SProxy "Var")
          (\(V n x) -> "(mkVar (V " <> show n <> show x <> "))")
        # Variant.on (SProxy :: SProxy "Embed")
          (\e -> "(mkEmbed (" <> show e <> "))")
        )
      # VariantF.on (SProxy :: SProxy "TextLit")
          (\e ->
            let
              v e' = case e' of
                TextLit s -> "(TextLit " <> show s <> ")"
                TextInterp s e'' m -> "(TextInterp " <> show s <> e'' <> v m <> ")"
            in "(mkTextLit " <> v e <> ")"
          )
      # VariantF.on (SProxy :: SProxy "Union")
        (\(Compose a) -> "(mkRecord " <> rec a <> ")")
      # VariantF.on (SProxy :: SProxy "UnionLit")
        (\(Product (Tuple (Tuple ty val) (Compose a))) -> "(mkUnionLit " <> ty <> val <> rec a <> ")")
      )

instance eqExpr :: (Eq s, Eq a) => Eq (Expr s a) where
  eq = unsafeCoerce (eq :: Mu (ExprRowVF s a) -> Mu (ExprRowVF s a) -> Boolean)

vfEqCase ::
  forall sym fnc v' v v1' v1 a.
    IsSymbol sym =>
    Eq (fnc a) =>
    Row.Cons sym (FProxy fnc) v' v =>
    Row.Cons sym (FProxy fnc) v1' v1 =>
  SProxy sym ->
  (VariantF v' a -> VariantF v1 a -> Boolean) ->
  VariantF v a -> VariantF v1 a -> Boolean
vfEqCase k = VariantF.on k (\a -> VariantF.default false # VariantF.on k (eq a))

newtype ExprRowVF s a b = ERVF (VariantF (ExprRow s a) b)
instance eq1ExprRowVF :: (Eq s, Eq a) => Eq1 (ExprRowVF s a) where
  eq1 (ERVF e1) (ERVF e2) =
    ( VariantF.case_
    # vfEqCase (SProxy :: SProxy "Annot")
    # vfEqCase (SProxy :: SProxy "App")
    # vfEqCase (SProxy :: SProxy "BinOp")
    # vfEqCase (SProxy :: SProxy "BoolIf")
    # vfEqCase (SProxy :: SProxy "Constructors")
    # vfEqCase (SProxy :: SProxy "Field")
    # vfEqCase (SProxy :: SProxy "Lam")
    # vfEqCase (SProxy :: SProxy "Let")
    # vfEqCase (SProxy :: SProxy "ListLit")
    # vfEqCase (SProxy :: SProxy "Merge")
    # vfEqCase (SProxy :: SProxy "Note")
    # vfEqCase (SProxy :: SProxy "OptionalLit")
    # vfEqCase (SProxy :: SProxy "Pi")
    # vfEqCase (SProxy :: SProxy "Project")
    # vfEqCase (SProxy :: SProxy "Record")
    # vfEqCase (SProxy :: SProxy "RecordLit")
    # vfEqCase (SProxy :: SProxy "SimpleThings")
    # vfEqCase (SProxy :: SProxy "TextLit")
    # vfEqCase (SProxy :: SProxy "Union")
    # vfEqCase (SProxy :: SProxy "UnionLit")
    ) e1 e2

instance bifunctorExpr :: Bifunctor Expr where
  bimap f g (Expr e) = Expr $ e # transMu
    ( VariantF.expand
    # VariantF.on (SProxy :: SProxy "SimpleThings")
      ( (<<<) (VariantF.inj (SProxy :: SProxy "SimpleThings"))
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
      ( (>>>) unwrap
      $ ( Variant.expand
      >>> ConstF.Const
      >>> VariantF.inj (SProxy :: SProxy "SimpleThings")
        )
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
-- (Bi)traversable will allow running computations on the embedded data,
-- e.g. using an error monad to get rid of holes, or using Aff to fill in
-- imports (especially via URL).
instance bitraversableExpr :: Bitraversable Expr where
  bisequence = bisequenceDefault
  bitraverse f g (Expr (In e)) = map (Expr <<< In) $
    ( ( traverse (Expr >>> bitraverse f g >>> map unwrap)
    >>> map VariantF.expand
      )
    # VariantF.on (SProxy :: SProxy "SimpleThings")
      ( (>>>) (unwrap)
      $ (<<<)
          ( map
            ( ConstF.Const
          >>> VariantF.inj (SProxy :: SProxy "SimpleThings")
            )
          )
      $ Variant.expand >>> pure
      # Variant.on (SProxy :: SProxy "Embed")
        (g >>> map (Variant.inj (SProxy :: SProxy "Embed")))
      )
    # VariantF.on (SProxy :: SProxy "Note")
      (\(Tuple a rest) -> Tuple <$> f a <*> bitraverse f g (Expr rest) <#>
        map unwrap >>> VariantF.inj (SProxy :: SProxy "Note")
      )
    ) e
instance traversableExpr :: Traversable (Expr s) where
  sequence = sequenceDefault
  traverse = bitraverse pure

-- A helper to coalesce a tree of annotations into a single annotation on
-- a "real" AST node.
unfurl :: forall s a. Monoid s =>
  Expr s a -> Tuple s (VariantF (AllTheThings ( "Embed" :: a ) ()) (Expr s a))
unfurl (Expr e0) = map (map Expr) $ go mempty e0 where
  go s = unroll >>>
    VariantF.on (SProxy :: SProxy "Note")
      (uncurry go)
      (Tuple s)

coalesce1 :: forall s a. Monoid s => Expr s a -> Expr s a
coalesce1 e = uncurry mkNote $ unfurl e <#>
  map unwrap >>> VariantF.expand >>> roll >>> Expr

-- Pris(o)ms of the behemoth
_ExprF :: forall a s unused f k.
  Row.Cons k (FProxy f) unused (ExprRow s a) =>
  IsSymbol k => Functor f =>
  SProxy k -> Prism' (Expr s a) (f (Expr s a))
_ExprF k = _E (_ExprFPrism k)

-- Convert a prism operating on VariantF ( ... ) Expr to one operating on Expr
_E :: forall f s a. Functor f =>
  Prism'
    (VariantF (ExprRow s a) (Expr s a))
    (f (Expr s a)) ->
  Prism' (Expr s a) (f (Expr s a))
_E p = _Newtype <<< _Newtype <<< mapIso (re _Newtype) <<< p where
    mapIso :: forall b c g. Functor g => Iso' b c -> Iso' (g b) (g c)
    mapIso i = iso (map (view i)) (map (review i))

type ExprFPrism r f = forall o. Prism' (VariantF r o) (f o)
_ExprFPrism :: forall r unused f k.
  Row.Cons k (FProxy f) unused r =>
  IsSymbol k => Functor f =>
  SProxy k -> ExprFPrism r f
_ExprFPrism k = prism' (VariantF.inj k)
  (VariantF.default Nothing # VariantF.on k Just)

_Expr :: forall a s unused v k.
  Row.Cons k v unused (SimpleThings ( "Embed" :: a )) =>
  IsSymbol k =>
  SProxy k -> Prism' (Expr s a) v
_Expr k = _E (_ExprPrism k) <<< _Newtype

type ExprPrism r v =
  forall r2.
    ExprFPrism
      ( "SimpleThings" :: FProxy (ConstF.Const (Variant r)) | r2 )
      (ConstF.Const v)

type SimplePrism r v =
  forall r2 o.
    Prism'
      (VariantF ( "SimpleThings" :: FProxy (ConstF.Const (Variant r)) | r2 ) o)
      v

_ExprPrism :: forall r unused v k.
  Row.Cons k v unused r =>
  IsSymbol k =>
  SProxy k ->
  ExprPrism r v
_ExprPrism k = _ExprFPrism (SProxy :: SProxy "SimpleThings")
  <<< _Newtype <<<
    prism' (Variant.inj k) (Variant.default Nothing # Variant.on k Just)
  <<< re _Newtype

_BinOp :: forall a s unused k.
  Row.Cons k Unit unused (BuiltinBinOps ()) =>
  IsSymbol k =>
  SProxy k -> Prism' (Expr s a) (Pair (Expr s a))
_BinOp k = _E (_BinOpPrism k)

type BinOpPrism r =
  forall r2.
    ExprFPrism
      ( "BinOp" :: FProxy (BinOpF r) | r2 )
      Pair
_BinOpPrism ::
  forall unused k r.
    Row.Cons k Unit unused r =>
    IsSymbol k =>
  SProxy k ->
  BinOpPrism r
_BinOpPrism k = _ExprFPrism (SProxy :: SProxy "BinOp") <<< prism'
  (\(Pair l r) -> BinOpF (Variant.inj k unit) l r)
  (\(BinOpF which l r) ->
    ( Variant.default Nothing
    # Variant.on k (\_ -> Just (Pair l r))
    ) which
  )

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

_Const :: forall r. ExprPrism ( "Const" :: Const | r ) Const
_Const = _ExprPrism (SProxy :: SProxy "Const")

mkVar :: forall s a. Var -> Expr s a
mkVar = mkExpr (SProxy :: SProxy "Var")

_Var :: forall r. ExprPrism ( "Var" :: Var | r ) Var
_Var = _ExprPrism (SProxy :: SProxy "Var")

mkLam :: forall s a. String -> Expr s a -> Expr s a -> Expr s a
mkLam name ty expr = mkExprF (SProxy :: SProxy "Lam")
  (product (Tuple name ty) (Identity expr))

_Lam :: forall r o.
  Prism' (VariantF ( "Lam" :: FProxy BindingBody | r ) o)
  { var :: String, ty :: o, body :: o }
_Lam = _ExprFPrism (SProxy :: SProxy "Lam") <<< _Newtype <<< iso into outof where
  into (Tuple (Tuple var ty) (Identity body)) = { var, ty, body }
  outof { var, ty, body } = (Tuple (Tuple var ty) (Identity body))

mkPi :: forall s a. String -> Expr s a -> Expr s a -> Expr s a
mkPi name ty expr = mkExprF (SProxy :: SProxy "Pi")
  (product (Tuple name ty) (Identity expr))

_Pi :: forall r o.
  Prism' (VariantF ( "Pi" :: FProxy BindingBody | r ) o)
  { var :: String, ty :: o, body :: o }
_Pi = _ExprFPrism (SProxy :: SProxy "Pi") <<< _Newtype <<< iso into outof where
  into (Tuple (Tuple var ty) (Identity body)) = { var, ty, body }
  outof { var, ty, body } = (Tuple (Tuple var ty) (Identity body))

mkApp :: forall s a. Expr s a -> Expr s a -> Expr s a
mkApp fn arg = mkExprF (SProxy :: SProxy "App")
  (Pair fn arg)

_App :: forall r o.
  Prism' (VariantF ( "App" :: FProxy Pair | r ) o)
  { fn :: o, arg :: o }
_App = _ExprFPrism (SProxy :: SProxy "App") <<< iso into outof where
  into (Pair fn arg) = { fn, arg }
  outof { fn, arg } = Pair fn arg

mkLet :: forall s a. String -> Maybe (Expr s a) -> Expr s a -> Expr s a -> Expr s a
mkLet name ty val expr = mkExprF (SProxy :: SProxy "Let")
  (LetF name ty val expr)

_Let :: forall r o.
  Prism' (VariantF ( "Let" :: FProxy LetF | r ) o)
  { var :: String
  , ty :: Maybe o
  , value :: o
  , body :: o
  }
_Let = _ExprFPrism (SProxy :: SProxy "Let") <<< iso into outof where
  into (LetF var ty value body) = { var, ty, value, body }
  outof { var, ty, value, body } = LetF var ty value body

mkAnnot :: forall s a. Expr s a -> Expr s a -> Expr s a
mkAnnot val ty = mkExprF (SProxy :: SProxy "Annot")
  (Pair val ty)

_Annot :: forall r o.
  Prism' (VariantF ( "Annot" :: FProxy Pair | r ) o)
  { value :: o, ty :: o }
_Annot = _ExprFPrism (SProxy :: SProxy "Annot") <<< iso into outof where
  into (Pair value ty) = { value, ty }
  outof { value, ty } = Pair value ty

mkBool :: forall s a. Expr s a
mkBool = mkExpr (SProxy :: SProxy "Bool") unit

_Bool :: forall r. ExprPrism ( "Bool" :: Unit | r ) Unit
_Bool = _ExprPrism (SProxy :: SProxy "Bool")

mkBoolLit :: forall s a. Boolean -> Expr s a
mkBoolLit = mkExpr (SProxy :: SProxy "BoolLit")

_BoolLit :: forall r. ExprPrism ( "BoolLit" :: Boolean | r ) Boolean
_BoolLit = _ExprPrism (SProxy :: SProxy "BoolLit")

_BoolLit_True :: forall r. SimplePrism ( "BoolLit" :: Boolean | r ) Unit
_BoolLit_True = _BoolLit <<< _Newtype <<< only true

_BoolLit_False :: forall r. SimplePrism ( "BoolLit" :: Boolean | r ) Unit
_BoolLit_False = _BoolLit <<< _Newtype <<< only false

mkBoolAnd :: forall s a. Expr s a -> Expr s a -> Expr s a
mkBoolAnd = mkBinOp (SProxy :: SProxy "BoolAnd")

_BoolAnd :: forall r. BinOpPrism ( "BoolAnd" :: Unit | r )
_BoolAnd = _BinOpPrism (SProxy :: SProxy "BoolAnd")

mkBoolOr :: forall s a. Expr s a -> Expr s a -> Expr s a
mkBoolOr = mkBinOp (SProxy :: SProxy "BoolOr")

_BoolOr :: forall r. BinOpPrism ( "BoolOr" :: Unit | r )
_BoolOr = _BinOpPrism (SProxy :: SProxy "BoolOr")

mkBoolEQ :: forall s a. Expr s a -> Expr s a -> Expr s a
mkBoolEQ = mkBinOp (SProxy :: SProxy "BoolEQ")

_BoolEQ :: forall r. BinOpPrism ( "BoolEQ" :: Unit | r )
_BoolEQ = _BinOpPrism (SProxy :: SProxy "BoolEQ")

mkBoolNE :: forall s a. Expr s a -> Expr s a -> Expr s a
mkBoolNE = mkBinOp (SProxy :: SProxy "BoolNE")

_BoolNE :: forall r. BinOpPrism ( "BoolNE" :: Unit | r )
_BoolNE = _BinOpPrism (SProxy :: SProxy "BoolNE")

mkBoolIf :: forall s a. Expr s a -> Expr s a -> Expr s a -> Expr s a
mkBoolIf cond t f = mkExprF (SProxy :: SProxy "BoolIf")
  (Triplet cond t f)

_BoolIf :: forall r. ExprFPrism ( "BoolIf" :: FProxy Triplet | r ) Triplet
_BoolIf = _ExprFPrism (SProxy :: SProxy "BoolIf")

mkNatural :: forall s a. Expr s a
mkNatural = mkExpr (SProxy :: SProxy "Natural") unit

_Natural :: forall r. ExprPrism ( "Natural" :: Unit | r ) Unit
_Natural = _ExprPrism (SProxy :: SProxy "Natural")

mkNaturalLit :: forall s a. Int -> Expr s a
mkNaturalLit = mkExpr (SProxy :: SProxy "NaturalLit")

_NaturalLit :: forall r. ExprPrism ( "NaturalLit" :: Int | r ) Int
_NaturalLit = _ExprPrism (SProxy :: SProxy "NaturalLit")

_NaturalLit_0 :: forall r. SimplePrism ( "NaturalLit" :: Int | r ) Unit
_NaturalLit_0 = _NaturalLit <<< _Newtype <<< only zero

_NaturalLit_1 :: forall r. SimplePrism ( "NaturalLit" :: Int | r ) Unit
_NaturalLit_1 = _NaturalLit <<< _Newtype <<< only one

mkNaturalFold :: forall s a. Expr s a
mkNaturalFold = mkExpr (SProxy :: SProxy "NaturalFold") unit

_NaturalFold :: forall r. ExprPrism ( "NaturalFold" :: Unit | r ) Unit
_NaturalFold = _ExprPrism (SProxy :: SProxy "NaturalFold")

mkNaturalBuild :: forall s a. Expr s a
mkNaturalBuild = mkExpr (SProxy :: SProxy "NaturalBuild") unit

_NaturalBuild :: forall r. ExprPrism ( "NaturalBuild" :: Unit | r ) Unit
_NaturalBuild = _ExprPrism (SProxy :: SProxy "NaturalBuild")

mkNaturalIsZero :: forall s a. Expr s a
mkNaturalIsZero = mkExpr (SProxy :: SProxy "NaturalIsZero") unit

_NaturalIsZero :: forall r. ExprPrism ( "NaturalIsZero" :: Unit | r ) Unit
_NaturalIsZero = _ExprPrism (SProxy :: SProxy "NaturalIsZero")

mkNaturalEven :: forall s a. Expr s a
mkNaturalEven = mkExpr (SProxy :: SProxy "NaturalEven") unit

_NaturalEven :: forall r. ExprPrism ( "NaturalEven" :: Unit | r ) Unit
_NaturalEven = _ExprPrism (SProxy :: SProxy "NaturalEven")

mkNaturalOdd :: forall s a. Expr s a
mkNaturalOdd = mkExpr (SProxy :: SProxy "NaturalOdd") unit

_NaturalOdd :: forall r. ExprPrism ( "NaturalOdd" :: Unit | r ) Unit
_NaturalOdd = _ExprPrism (SProxy :: SProxy "NaturalOdd")

mkNaturalToInteger :: forall s a. Expr s a
mkNaturalToInteger = mkExpr (SProxy :: SProxy "NaturalToInteger") unit

_NaturalToInteger :: forall r. ExprPrism ( "NaturalToInteger" :: Unit | r ) Unit
_NaturalToInteger = _ExprPrism (SProxy :: SProxy "NaturalToInteger")

mkNaturalShow :: forall s a. Expr s a
mkNaturalShow = mkExpr (SProxy :: SProxy "NaturalShow") unit

_NaturalShow :: forall r. ExprPrism ( "NaturalShow" :: Unit | r ) Unit
_NaturalShow = _ExprPrism (SProxy :: SProxy "NaturalShow")

mkNaturalPlus :: forall s a. Expr s a -> Expr s a -> Expr s a
mkNaturalPlus = mkBinOp (SProxy :: SProxy "NaturalPlus")

_NaturalPlus :: forall r. BinOpPrism ( "NaturalPlus" :: Unit | r )
_NaturalPlus = _BinOpPrism (SProxy :: SProxy "NaturalPlus")

mkNaturalTimes :: forall s a. Expr s a -> Expr s a -> Expr s a
mkNaturalTimes = mkBinOp (SProxy :: SProxy "NaturalTimes")

_NaturalTimes :: forall r. BinOpPrism ( "NaturalTimes" :: Unit | r )
_NaturalTimes = _BinOpPrism (SProxy :: SProxy "NaturalTimes")

mkInteger :: forall s a. Expr s a
mkInteger = mkExpr (SProxy :: SProxy "Integer") unit

_Integer :: forall r. ExprPrism ( "Integer" :: Unit | r ) Unit
_Integer = _ExprPrism (SProxy :: SProxy "Integer")

mkIntegerLit :: forall s a. Int -> Expr s a
mkIntegerLit = mkExpr (SProxy :: SProxy "IntegerLit")

_IntegerLit :: forall r. ExprPrism ( "IntegerLit" :: Int | r ) Int
_IntegerLit = _ExprPrism (SProxy :: SProxy "IntegerLit")

mkIntegerShow :: forall s a. Expr s a
mkIntegerShow = mkExpr (SProxy :: SProxy "IntegerShow") unit

_IntegerShow :: forall r. ExprPrism ( "IntegerShow" :: Unit | r ) Unit
_IntegerShow = _ExprPrism (SProxy :: SProxy "IntegerShow")

mkIntegerToDouble :: forall s a. Expr s a
mkIntegerToDouble = mkExpr (SProxy :: SProxy "IntegerToDouble") unit

_IntegerToDouble :: forall r. ExprPrism ( "IntegerToDouble" :: Unit | r ) Unit
_IntegerToDouble = _ExprPrism (SProxy :: SProxy "IntegerToDouble")

mkDouble :: forall s a. Expr s a
mkDouble = mkExpr (SProxy :: SProxy "Double") unit

_Double :: forall r. ExprPrism ( "Double" :: Unit | r ) Unit
_Double = _ExprPrism (SProxy :: SProxy "Double")

mkDoubleLit :: forall s a. Number -> Expr s a
mkDoubleLit = mkExpr (SProxy :: SProxy "DoubleLit")

_DoubleLit :: forall r. ExprPrism ( "DoubleLit" :: Number | r ) Number
_DoubleLit = _ExprPrism (SProxy :: SProxy "DoubleLit")

mkDoubleShow :: forall s a. Expr s a
mkDoubleShow = mkExpr (SProxy :: SProxy "DoubleShow") unit

_DoubleShow :: forall r. ExprPrism ( "DoubleShow" :: Unit | r ) Unit
_DoubleShow = _ExprPrism (SProxy :: SProxy "DoubleShow")

mkText :: forall s a. Expr s a
mkText = mkExpr (SProxy :: SProxy "Text") unit

_Text :: forall r. ExprPrism ( "Text" :: Unit | r ) Unit
_Text = _ExprPrism (SProxy :: SProxy "Text")

mkTextLit :: forall s a. TextLitF (Expr s a) -> Expr s a
mkTextLit = mkExprF (SProxy :: SProxy "TextLit")

_TextLit :: forall r. ExprFPrism ( "TextLit" :: FProxy TextLitF | r ) TextLitF
_TextLit = _ExprFPrism (SProxy :: SProxy "TextLit")

_TextLit_empty :: forall r o. Prism' (VariantF ( "TextLit" :: FProxy TextLitF | r ) o) Unit
_TextLit_empty = _TextLit <<< prism' (const (TextLit ""))
  case _ of
    TextLit "" -> Just unit
    _ -> Nothing

mkTextAppend :: forall s a. Expr s a -> Expr s a -> Expr s a
mkTextAppend = mkBinOp (SProxy :: SProxy "TextAppend")

_TextAppend :: forall r. BinOpPrism ( "TextAppend" :: Unit | r )
_TextAppend = _BinOpPrism (SProxy :: SProxy "TextAppend")

mkList :: forall s a. Expr s a
mkList = mkExpr (SProxy :: SProxy "List") unit

_List :: forall r. ExprPrism ( "List" :: Unit | r ) Unit
_List = _ExprPrism (SProxy :: SProxy "List")

mkListLit :: forall s a. Maybe (Expr s a) -> Array (Expr s a) -> Expr s a
mkListLit ty lit = mkExprF (SProxy :: SProxy "ListLit")
  (product ty lit)

_ListLit :: forall r o.
  Prism' (VariantF ( "ListLit" :: FProxy (Product Maybe Array) | r ) o)
  { ty :: Maybe o, values :: Array o }
_ListLit = _ExprFPrism (SProxy :: SProxy "ListLit") <<< _Newtype <<< iso into outof where
  into (Tuple ty values) = { ty, values }
  outof { ty, values } = Tuple ty values

mkListAppend :: forall s a. Expr s a -> Expr s a -> Expr s a
mkListAppend = mkBinOp (SProxy :: SProxy "ListAppend")

_ListAppend :: forall r. BinOpPrism ( "ListAppend" :: Unit | r )
_ListAppend = _BinOpPrism (SProxy :: SProxy "ListAppend")

mkListFold :: forall s a. Expr s a
mkListFold = mkExpr (SProxy :: SProxy "ListFold") unit

_ListFold :: forall r. ExprPrism ( "ListFold" :: Unit | r ) Unit
_ListFold = _ExprPrism (SProxy :: SProxy "ListFold")

mkListBuild :: forall s a. Expr s a
mkListBuild = mkExpr (SProxy :: SProxy "ListBuild") unit

_ListBuild :: forall r. ExprPrism ( "ListBuild" :: Unit | r ) Unit
_ListBuild = _ExprPrism (SProxy :: SProxy "ListBuild")

mkListLength :: forall s a. Expr s a
mkListLength = mkExpr (SProxy :: SProxy "ListLength") unit

_ListLength :: forall r. ExprPrism ( "ListLength" :: Unit | r ) Unit
_ListLength = _ExprPrism (SProxy :: SProxy "ListLength")

mkListHead :: forall s a. Expr s a
mkListHead = mkExpr (SProxy :: SProxy "ListHead") unit

_ListHead :: forall r. ExprPrism ( "ListHead" :: Unit | r ) Unit
_ListHead = _ExprPrism (SProxy :: SProxy "ListHead")

mkListLast :: forall s a. Expr s a
mkListLast = mkExpr (SProxy :: SProxy "ListLast") unit

_ListLast :: forall r. ExprPrism ( "ListLast" :: Unit | r ) Unit
_ListLast = _ExprPrism (SProxy :: SProxy "ListLast")

mkListIndexed :: forall s a. Expr s a
mkListIndexed = mkExpr (SProxy :: SProxy "ListIndexed") unit

_ListIndexed :: forall r. ExprPrism ( "ListIndexed" :: Unit | r ) Unit
_ListIndexed = _ExprPrism (SProxy :: SProxy "ListIndexed")

mkListReverse :: forall s a. Expr s a
mkListReverse = mkExpr (SProxy :: SProxy "ListReverse") unit

_ListReverse :: forall r. ExprPrism ( "ListReverse" :: Unit | r ) Unit
_ListReverse = _ExprPrism (SProxy :: SProxy "ListReverse")

mkOptional :: forall s a. Expr s a
mkOptional = mkExpr (SProxy :: SProxy "Optional") unit

_Optional :: forall r. ExprPrism ( "Optional" :: Unit | r ) Unit
_Optional = _ExprPrism (SProxy :: SProxy "Optional")

mkOptionalLit :: forall s a. Expr s a -> Maybe (Expr s a) -> Expr s a
mkOptionalLit ty lit = mkExprF (SProxy :: SProxy "OptionalLit")
  (product (Identity ty) lit)

_OptionalLit :: forall r o.
  Prism' (VariantF ( "OptionalLit" :: FProxy (Product Identity Maybe) | r ) o)
  { ty :: o, value :: Maybe o }
_OptionalLit = _ExprFPrism (SProxy :: SProxy "OptionalLit") <<< _Newtype <<< iso into outof where
  into (Tuple (Identity ty) value) = { ty, value }
  outof { ty, value } = Tuple (Identity ty) value

mkOptionalFold :: forall s a. Expr s a
mkOptionalFold = mkExpr (SProxy :: SProxy "OptionalFold") unit

_OptionalFold :: forall r. ExprPrism ( "OptionalFold" :: Unit | r ) Unit
_OptionalFold = _ExprPrism (SProxy :: SProxy "OptionalFold")

mkOptionalBuild :: forall s a. Expr s a
mkOptionalBuild = mkExpr (SProxy :: SProxy "OptionalBuild") unit

_OptionalBuild :: forall r. ExprPrism ( "OptionalBuild" :: Unit | r ) Unit
_OptionalBuild = _ExprPrism (SProxy :: SProxy "OptionalBuild")

mkRecord :: forall s a. Array (Tuple String (Expr s a)) -> Expr s a
mkRecord = mkExprF (SProxy :: SProxy "Record") <<< Compose

_Record :: forall r. ExprFPrism
  ( "Record" :: FProxy (OrdMap String) | r ) (OrdMap String)
_Record = _ExprFPrism (SProxy :: SProxy "Record")

_Record_empty :: forall r o.
  Prism' (VariantF ( "Record" :: FProxy (OrdMap String) | r ) o) Unit
_Record_empty = _Record <<< prism' (const (Compose [])) case _ of
  Compose [] -> Just unit
  _ -> Nothing

mkRecordLit :: forall s a. Array (Tuple String (Expr s a)) -> Expr s a
mkRecordLit = mkExprF (SProxy :: SProxy "RecordLit") <<< Compose

_RecordLit :: forall r. ExprFPrism
  ( "RecordLit" :: FProxy (OrdMap String) | r ) (OrdMap String)
_RecordLit = _ExprFPrism (SProxy :: SProxy "RecordLit")

_RecordLit_empty :: forall r o.
  Prism' (VariantF ( "RecordLit" :: FProxy (OrdMap String) | r ) o) Unit
_RecordLit_empty = _RecordLit <<< prism' (const (Compose [])) case _ of
  Compose [] -> Just unit
  _ -> Nothing

mkUnion :: forall s a. Array (Tuple String (Expr s a)) -> Expr s a
mkUnion = mkExprF (SProxy :: SProxy "Union") <<< Compose

_Union :: forall r. ExprFPrism ( "Union" :: FProxy (OrdMap String) | r ) (OrdMap String)
_Union = _ExprFPrism (SProxy :: SProxy "Union")

_Union_empty :: forall r o.
  Prism' (VariantF ( "Union" :: FProxy (OrdMap String) | r ) o) Unit
_Union_empty = _Union <<< prism' (const (Compose [])) case _ of
  Compose [] -> Just unit
  _ -> Nothing

mkUnionLit :: forall s a. String -> Expr s a -> Array (Tuple String (Expr s a)) -> Expr s a
mkUnionLit name value others = mkExprF (SProxy :: SProxy "UnionLit")
  (product (Tuple name value) (Compose others))

_UnionLit :: forall r o. Prism'
  (VariantF ( "UnionLit" :: FProxy (Product (Tuple String) (OrdMap String)) | r ) o)
  { label :: String, value :: o, tys :: OrdMap String o }
_UnionLit = _ExprFPrism (SProxy :: SProxy "UnionLit") <<< _Newtype <<< iso into outof where
  into (Tuple (Tuple label value) tys) = { label, value, tys }
  outof { label, value, tys } = Tuple (Tuple label value) tys

mkCombine :: forall s a. Expr s a -> Expr s a -> Expr s a
mkCombine = mkBinOp (SProxy :: SProxy "Combine")

_Combine :: forall r. BinOpPrism ( "Combine" :: Unit | r )
_Combine = _BinOpPrism (SProxy :: SProxy "Combine")

mkCombineTypes :: forall s a. Expr s a -> Expr s a -> Expr s a
mkCombineTypes = mkBinOp (SProxy :: SProxy "CombineTypes")

_CombineTypes :: forall r. BinOpPrism ( "CombineTypes" :: Unit | r )
_CombineTypes = _BinOpPrism (SProxy :: SProxy "CombineTypes")

mkPrefer :: forall s a. Expr s a -> Expr s a -> Expr s a
mkPrefer = mkBinOp (SProxy :: SProxy "Prefer")

_Prefer :: forall r. BinOpPrism ( "Prefer" :: Unit | r )
_Prefer = _BinOpPrism (SProxy :: SProxy "Prefer")

mkMerge :: forall s a. Expr s a -> Expr s a -> Maybe (Expr s a) -> Expr s a
mkMerge x y t = mkExprF (SProxy :: SProxy "Merge")
  (MergeF x y t)

_Merge :: forall r. ExprFPrism ( "Merge" :: FProxy MergeF | r ) MergeF
_Merge = _ExprFPrism (SProxy :: SProxy "Merge")

mkConstructors :: forall s a. Expr s a -> Expr s a
mkConstructors = mkExprF (SProxy :: SProxy "Constructors") <<< Identity

_Constructors :: forall r o.
  Prism' (VariantF ( "Constructors" :: FProxy Identity | r ) o) o
_Constructors = _ExprFPrism (SProxy :: SProxy "Constructors") <<< _Newtype

mkField :: forall s a. Expr s a -> String -> Expr s a
mkField expr field = mkExprF (SProxy :: SProxy "Field")
  (Tuple field expr)

_Field :: forall r o. Prism'
  (VariantF ( "Field" :: FProxy (Tuple String) | r ) o)
  (Tuple o String)
_Field = _ExprFPrism (SProxy :: SProxy "Field") <<< iso swap swap

mkProject :: forall s a. Expr s a -> Set String -> Expr s a
mkProject expr fields = mkExprF (SProxy :: SProxy "Project")
  (Tuple fields expr)

_Project :: forall r o. Prism'
  (VariantF ( "Project" :: FProxy (Tuple (Set String)) | r ) o)
  (Tuple o (Set String))
_Project = _ExprFPrism (SProxy :: SProxy "Project") <<< iso swap swap

mkNote :: forall s a. s -> Expr s a -> Expr s a
mkNote note expr = mkExprF (SProxy :: SProxy "Note")
  (Tuple note expr)

_Note :: forall s r. ExprFPrism ( "Note" :: FProxy (Tuple s) | r ) (Tuple s)
_Note = _ExprFPrism (SProxy :: SProxy "Note")

mkImportAlt :: forall s a. Expr s a -> Expr s a -> Expr s a
mkImportAlt = mkBinOp (SProxy :: SProxy "ImportAlt")

_ImportAlt :: forall r. BinOpPrism ( "ImportAlt" :: Unit | r )
_ImportAlt = _BinOpPrism (SProxy :: SProxy "ImportAlt")

mkEmbed :: forall s a. a -> Expr s a
mkEmbed = mkExpr (SProxy :: SProxy "Embed")

_Embed :: forall a r. ExprPrism ( "Embed" :: a | r ) a
_Embed = _ExprPrism (SProxy :: SProxy "Embed")

module Dhall.Core.AST where

import Prelude

import Control.Monad.Free (Free, hoistFree)
import Data.Bifoldable (class Bifoldable, bifoldMap, bifoldl, bifoldr)
import Data.Bifunctor (class Bifunctor, lmap)
import Data.Bitraversable (class Bitraversable, bitraverse, bisequenceDefault)
import Data.Const as ConstF
import Data.Either (Either(..), either)
import Data.Eq (class Eq1, eq1)
import Data.Foldable (class Foldable, foldMap, foldl, foldr, foldrDefault)
import Data.FoldableWithIndex (class FoldableWithIndex, foldMapWithIndex)
import Data.Functor.Product (Product(..), product)
import Data.Functor.Variant (VariantF)
import Data.Functor.Variant as VariantF
import Data.Identity (Identity(..))
import Data.Lens (Prism', prism', iso, only)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Maybe (Maybe(..))
import Data.Natural (Natural)
import Data.Newtype (class Newtype, un, unwrap, wrap)
import Data.Set (Set)
import Data.String (joinWith)
import Data.Symbol (class IsSymbol, SProxy(..))
import Data.Traversable (class Traversable, sequenceDefault, traverse)
import Data.Tuple (Tuple(..), uncurry, swap)
import Data.Variant.Internal (FProxy)
import Dhall.Core.StrMapIsh (class StrMapIsh)
import Dhall.Core.StrMapIsh as StrMapIsh
import Matryoshka (class Corecursive, class Recursive, cata, embed, project)
import Prim.Row as Row
import Type.Row (type (+))

type CONST a = FProxy (ConstF.Const a)
type UNIT = CONST Unit

data Const = Type | Kind
derive instance eqConst :: Eq Const
derive instance ordConst :: Ord Const

data Var = V String Int
derive instance eqVar :: Eq Var
derive instance ordVar :: Ord Var

type Literals (m :: Type -> Type) vs =
  ( "BoolLit" :: CONST Boolean
  , "NaturalLit" :: CONST Natural
  , "IntegerLit" :: CONST Int
  , "DoubleLit" :: CONST Number
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

type Literals2 (m :: Type -> Type) v =
  ( "TextLit" :: FProxy TextLitF
  , "ListLit" :: FProxy (Product Maybe Array)
  , "OptionalLit" :: FProxy (Product Identity Maybe)
  , "RecordLit" :: FProxy m
  , "UnionLit" :: FProxy (Product (Tuple String) m)
  | v
  )

type BuiltinTypes (m :: Type -> Type) vs =
  ( "Bool" :: UNIT
  , "Natural" :: UNIT
  , "Integer" :: UNIT
  , "Double" :: UNIT
  , "Text" :: UNIT
  , "List" :: UNIT
  , "Optional" :: UNIT
  | vs
  )

type BuiltinTypes2 (m :: Type -> Type) v =
  ( "Record" :: FProxy m
  , "Union" :: FProxy m
  | v
  )

type BuiltinFuncs (m :: Type -> Type) vs =
  ( "NaturalFold" :: UNIT
  , "NaturalBuild" :: UNIT
  , "NaturalIsZero" :: UNIT
  , "NaturalEven" :: UNIT
  , "NaturalOdd" :: UNIT
  , "NaturalToInteger" :: UNIT
  , "NaturalShow" :: UNIT
  , "IntegerShow" :: UNIT
  , "IntegerToDouble" :: UNIT
  , "DoubleShow" :: UNIT
  , "ListBuild" :: UNIT
  , "ListFold" :: UNIT
  , "ListLength" :: UNIT
  , "ListHead" :: UNIT
  , "ListLast" :: UNIT
  , "ListIndexed" :: UNIT
  , "ListReverse" :: UNIT
  , "OptionalFold" :: UNIT
  , "OptionalBuild" :: UNIT
  | vs
  )

type BuiltinBinOps (m :: Type -> Type) vs =
  ( "BoolAnd" :: FProxy Pair
  , "BoolOr" :: FProxy Pair
  , "BoolEQ" :: FProxy Pair
  , "BoolNE" :: FProxy Pair
  , "NaturalPlus" :: FProxy Pair
  , "NaturalTimes" :: FProxy Pair
  , "TextAppend" :: FProxy Pair
  , "ListAppend" :: FProxy Pair
  , "Combine" :: FProxy Pair
  , "CombineTypes" :: FProxy Pair
  , "Prefer" :: FProxy Pair
  , "ImportAlt" :: FProxy Pair
  | vs
  )

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

type BuiltinOps (m :: Type -> Type) v = BuiltinBinOps m
  ( "BoolIf" :: FProxy (Triplet)
  , "Field" :: FProxy (Tuple String)
  , "Project" :: FProxy (Tuple (Set String))
  , "Merge" :: FProxy (MergeF)
  , "Constructors" :: FProxy Identity
  | v
  )

type Terminals (m :: Type -> Type) vs =
  ( "Const" :: CONST Const
  , "Var" :: CONST Var
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

type Syntax (m :: Type -> Type) v =
  ( "Lam" :: FProxy (BindingBody)
  , "Pi" :: FProxy (BindingBody)
  , "App" :: FProxy (Pair)
  , "Let" :: FProxy LetF
  , "Annot" :: FProxy (Pair)
  | v
  )

type SimpleThings m vs = Literals m + BuiltinTypes m + BuiltinFuncs m + Terminals m + vs

type FunctorThings m v = Literals2 m + BuiltinTypes2 m + BuiltinOps m + Syntax m + v

type AllTheThings m v = SimpleThings m + FunctorThings m + v

type ExprRow m s =
  AllTheThings m
    ( "Note" :: FProxy (Tuple s)
    )
type ExprLayerRow m s a =
  AllTheThings m
    ( "Note" :: FProxy (Tuple s)
    , "Embed" :: CONST a
    )
type ExprLayerF m s a = VariantF (ExprLayerRow m s a)
type ExprLayer m s a = (ExprLayerF m s a) (Expr m s a)

newtype Expr m s a = Expr (Free (VariantF (ExprRow m s)) a)
derive instance newtypeExpr :: Newtype (Expr m s a) _

instance recursiveExpr :: Recursive (Expr m s a) (ExprRowVF m s a) where
  project = unwrap >>> project >>> map Expr >>> unwrap >>> either
    (wrap >>> VariantF.inj (SProxy :: SProxy "Embed"))
    VariantF.expand >>> ERVF

instance corecursiveExpr :: Corecursive (Expr m s a) (ExprRowVF m s a) where
  embed = wrap <<< embed <<< map (un Expr) <<< wrap <<<
    VariantF.on (SProxy :: SProxy "Embed") (Left <<< unwrap) Right <<< un ERVF

projectW :: forall m s a. Expr m s a -> ExprLayer m s a
projectW = project >>> unwrap

embedW :: forall m s a. ExprLayer m s a -> Expr m s a
embedW = embed <<< wrap


-- | Just a helper to handle recursive rewrites: top-down, requires explicit
-- | recursion for the cases that are handled by the rewrite.
rewriteTopDown :: forall r r' m s t a b.
  Row.Union r r' (ExprLayerRow m t b) =>
  (
    (VariantF r (Expr m s a) -> Expr m t b) ->
    VariantF (ExprLayerRow m s a) (Expr m s a) ->
    Expr m t b
  ) ->
  Expr m s a -> Expr m t b
rewriteTopDown rw1 = go where
  go expr = rw1 (map go >>> VariantF.expand >>> embedW) $ projectW expr

-- | Another recursion helper: bottom-up, recursion already happens before
-- | the rewrite gets ahold of it. Just follow the types.
rewriteBottomUp :: forall r r' m s t a b.
  Row.Union r r' (ExprLayerRow m t b) =>
  (
    (VariantF r (Expr m t b) -> Expr m t b) ->
    VariantF (ExprLayerRow m s a) (Expr m t b) ->
    Expr m t b
  ) ->
  Expr m s a -> Expr m t b
rewriteBottomUp rw1 = go where
  go expr = rw1 (VariantF.expand >>> embedW) $ go <$> projectW expr


instance showExpr :: (FoldableWithIndex String m, Show s, Show a) => Show (Expr m s a) where
  show (Expr e0) = cata show1 e0 where
    lits e = "[" <> joinWith ", " e <> "]"
    rec e = lits $ foldMapWithIndex (\k v -> ["(Tuple " <> show k <> v <> ")"]) e
    mb =
      case _ of
        Nothing -> "(Nothing)"
        Just s -> "(Just " <> s <> ")"
    binop tag (Pair l r) = "(mk" <> tag <> " " <> l <> r <> ")"
    show1 = unwrap >>> either (\e -> "(mkEmbed (" <> show e <> "))")
      ( VariantF.case_
      # VariantF.on (SProxy :: SProxy "Annot")
        (\(Pair l r) -> "(mkAnnot " <> l <> r <> ")")
      # VariantF.on (SProxy :: SProxy "App")
        (\(Pair l r) -> "(mkApp " <> l <> r <> ")")
      # VariantF.on (SProxy :: SProxy "BoolAnd") (binop "BoolAnd")
      # VariantF.on (SProxy :: SProxy "BoolOr") (binop "BoolOr")
      # VariantF.on (SProxy :: SProxy "BoolEQ") (binop "BoolEQ")
      # VariantF.on (SProxy :: SProxy "BoolNE") (binop "BoolNE")
      # VariantF.on (SProxy :: SProxy "NaturalPlus") (binop "NaturalPlus")
      # VariantF.on (SProxy :: SProxy "NaturalTimes") (binop "NaturalTimes")
      # VariantF.on (SProxy :: SProxy "TextAppend") (binop "TextAppend")
      # VariantF.on (SProxy :: SProxy "ListAppend") (binop "ListAppend")
      # VariantF.on (SProxy :: SProxy "Combine") (binop "Combine")
      # VariantF.on (SProxy :: SProxy "CombineTypes") (binop "CombineTypes")
      # VariantF.on (SProxy :: SProxy "Prefer") (binop "Prefer")
      # VariantF.on (SProxy :: SProxy "ImportAlt") (binop "ImportAlt")
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
        (\a -> "(mkRecord " <> rec a <> ")")
      # VariantF.on (SProxy :: SProxy "RecordLit")
        (\a -> "(mkRecord " <> rec a <> ")")
      # VariantF.on (SProxy :: SProxy "BoolLit")
        (unwrap >>> \b -> "(mkBoolLit " <> show b <> ")")
      # VariantF.on (SProxy :: SProxy "NaturalLit")
        (unwrap >>> \b -> "(mkNaturalLit " <> show b <> ")")
      # VariantF.on (SProxy :: SProxy "IntegerLit")
        (unwrap >>> \b -> "(mkIntegerLit " <> show b <> ")")
      # VariantF.on (SProxy :: SProxy "DoubleLit")
        (unwrap >>> \b -> "(mkDoubleLit " <> show b <> ")")
      # VariantF.on (SProxy :: SProxy "Bool") (const "mkBool")
      # VariantF.on (SProxy :: SProxy "Natural") (const "mkNatural")
      # VariantF.on (SProxy :: SProxy "Integer") (const "mkInteger")
      # VariantF.on (SProxy :: SProxy "Double") (const "mkDouble")
      # VariantF.on (SProxy :: SProxy "Text") (const "mkText")
      # VariantF.on (SProxy :: SProxy "List") (const "mkList")
      # VariantF.on (SProxy :: SProxy "Optional") (const "mkOptional")
      # VariantF.on (SProxy :: SProxy "NaturalFold") (const "mkNaturalFold")
      # VariantF.on (SProxy :: SProxy "NaturalBuild") (const "mkNaturalBuild")
      # VariantF.on (SProxy :: SProxy "NaturalIsZero") (const "mkNaturalIsZero")
      # VariantF.on (SProxy :: SProxy "NaturalEven") (const "mkNaturalEven")
      # VariantF.on (SProxy :: SProxy "NaturalOdd") (const "mkNaturalOdd")
      # VariantF.on (SProxy :: SProxy "NaturalToInteger") (const "mkNaturalToInteger")
      # VariantF.on (SProxy :: SProxy "NaturalShow") (const "mkNaturalShow")
      # VariantF.on (SProxy :: SProxy "IntegerShow") (const "mkIntegerShow")
      # VariantF.on (SProxy :: SProxy "IntegerToDouble") (const "mkIntegerToDouble")
      # VariantF.on (SProxy :: SProxy "DoubleShow") (const "mkDoubleShow")
      # VariantF.on (SProxy :: SProxy "ListBuild") (const "mkListBuild")
      # VariantF.on (SProxy :: SProxy "ListFold") (const "mkListFold")
      # VariantF.on (SProxy :: SProxy "ListLength") (const "mkListLength")
      # VariantF.on (SProxy :: SProxy "ListHead") (const "mkListHead")
      # VariantF.on (SProxy :: SProxy "ListLast") (const "mkListLast")
      # VariantF.on (SProxy :: SProxy "ListIndexed") (const "mkListIndexed")
      # VariantF.on (SProxy :: SProxy "ListReverse") (const "mkListReverse")
      # VariantF.on (SProxy :: SProxy "OptionalFold") (const "mkOptionalFold")
      # VariantF.on (SProxy :: SProxy "OptionalBuild") (const "mkOptionalBuild")
      # VariantF.on (SProxy :: SProxy "Const")
        (case _ of
          ConstF.Const Type -> "(mkConst Type)"
          ConstF.Const Kind -> "(mkConst Kind)"
        )
      # VariantF.on (SProxy :: SProxy "Var")
        (unwrap >>> \(V n x) -> "(mkVar (V " <> show n <> show x <> "))")
      # VariantF.on (SProxy :: SProxy "TextLit")
          (\e ->
            let
              v e' = case e' of
                TextLit s -> "(TextLit " <> show s <> ")"
                TextInterp s e'' m -> "(TextInterp " <> show s <> e'' <> v m <> ")"
            in "(mkTextLit " <> v e <> ")"
          )
      # VariantF.on (SProxy :: SProxy "Union")
        (\a -> "(mkRecord " <> rec a <> ")")
      # VariantF.on (SProxy :: SProxy "UnionLit")
        (\(Product (Tuple (Tuple ty val) a)) -> "(mkUnionLit " <> ty <> val <> rec a <> ")")
      )

instance eqExpr :: (Eq1 m, Eq s, Eq a) => Eq (Expr m s a) where
  eq e1 e2 = project e1 `eq1` project e2

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

vfEq1Case ::
  forall sym fnc v' v v1' v1 a.
    IsSymbol sym =>
    Eq1 fnc =>
    Eq a =>
    Row.Cons sym (FProxy fnc) v' v =>
    Row.Cons sym (FProxy fnc) v1' v1 =>
  SProxy sym ->
  (VariantF v' a -> VariantF v1 a -> Boolean) ->
  VariantF v a -> VariantF v1 a -> Boolean
vfEq1Case k = VariantF.on k (\a -> VariantF.default false # VariantF.on k (eq1 a))

newtype ExprRowVF m s a b = ERVF (ExprLayerF m s a b)
derive instance newtypeERVF :: Newtype (ExprRowVF m s a b) _
derive newtype instance functorERVF :: Functor (ExprRowVF m s a)
instance eq1ExprRowVF :: (Eq1 m, Eq s, Eq a) => Eq1 (ExprRowVF m s a) where
  eq1 (ERVF e1) (ERVF e2) =
    ( VariantF.case_
    # vfEqCase (SProxy :: SProxy "Annot")
    # vfEqCase (SProxy :: SProxy "App")
    # vfEqCase (SProxy :: SProxy "BoolAnd")
    # vfEqCase (SProxy :: SProxy "BoolOr")
    # vfEqCase (SProxy :: SProxy "BoolEQ")
    # vfEqCase (SProxy :: SProxy "BoolNE")
    # vfEqCase (SProxy :: SProxy "NaturalPlus")
    # vfEqCase (SProxy :: SProxy "NaturalTimes")
    # vfEqCase (SProxy :: SProxy "TextAppend")
    # vfEqCase (SProxy :: SProxy "ListAppend")
    # vfEqCase (SProxy :: SProxy "Combine")
    # vfEqCase (SProxy :: SProxy "CombineTypes")
    # vfEqCase (SProxy :: SProxy "Prefer")
    # vfEqCase (SProxy :: SProxy "ImportAlt")
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
    # vfEq1Case (SProxy :: SProxy "Record")
    # vfEq1Case (SProxy :: SProxy "RecordLit")
    # vfEqCase (SProxy :: SProxy "BoolLit")
    # vfEqCase (SProxy :: SProxy "NaturalLit")
    # vfEqCase (SProxy :: SProxy "IntegerLit")
    # vfEqCase (SProxy :: SProxy "DoubleLit")
    # vfEqCase (SProxy :: SProxy "Bool")
    # vfEqCase (SProxy :: SProxy "Natural")
    # vfEqCase (SProxy :: SProxy "Integer")
    # vfEqCase (SProxy :: SProxy "Double")
    # vfEqCase (SProxy :: SProxy "Text")
    # vfEqCase (SProxy :: SProxy "List")
    # vfEqCase (SProxy :: SProxy "Optional")
    # vfEqCase (SProxy :: SProxy "NaturalFold")
    # vfEqCase (SProxy :: SProxy "NaturalBuild")
    # vfEqCase (SProxy :: SProxy "NaturalIsZero")
    # vfEqCase (SProxy :: SProxy "NaturalEven")
    # vfEqCase (SProxy :: SProxy "NaturalOdd")
    # vfEqCase (SProxy :: SProxy "NaturalToInteger")
    # vfEqCase (SProxy :: SProxy "NaturalShow")
    # vfEqCase (SProxy :: SProxy "IntegerShow")
    # vfEqCase (SProxy :: SProxy "IntegerToDouble")
    # vfEqCase (SProxy :: SProxy "DoubleShow")
    # vfEqCase (SProxy :: SProxy "ListBuild")
    # vfEqCase (SProxy :: SProxy "ListFold")
    # vfEqCase (SProxy :: SProxy "ListLength")
    # vfEqCase (SProxy :: SProxy "ListHead")
    # vfEqCase (SProxy :: SProxy "ListLast")
    # vfEqCase (SProxy :: SProxy "ListIndexed")
    # vfEqCase (SProxy :: SProxy "ListReverse")
    # vfEqCase (SProxy :: SProxy "OptionalFold")
    # vfEqCase (SProxy :: SProxy "OptionalBuild")
    # vfEqCase (SProxy :: SProxy "Const")
    # vfEqCase (SProxy :: SProxy "Var")
    # vfEqCase (SProxy :: SProxy "Embed")
    # vfEqCase (SProxy :: SProxy "TextLit")
    # vfEq1Case (SProxy :: SProxy "Union")
    # vfEq1Case (SProxy :: SProxy "UnionLit")
    ) e1 e2

instance bifunctorExpr :: Functor m => Bifunctor (Expr m) where
  bimap f g (Expr e) = Expr $ e <#> g # hoistFree
    ( VariantF.expand
    # VariantF.on (SProxy :: SProxy "Note")
      (lmap f >>> VariantF.inj (SProxy :: SProxy "Note"))
    )
derive newtype instance functorExpr :: Functor (Expr m s)
derive newtype instance applyExpr :: Apply (Expr m s)
derive newtype instance applicativeExpr :: Applicative (Expr m s)
derive newtype instance bindExpr :: Bind (Expr m s)
derive newtype instance monadExpr :: Monad (Expr m s)

instance bifoldableExpr :: Foldable m => Bifoldable (Expr m) where
  bifoldMap f g e =
    ( foldMap (bifoldMap f g)
    # VariantF.on (SProxy :: SProxy "Embed") (unwrap >>> g)
    # VariantF.on (SProxy :: SProxy "Note")
      (\(Tuple s rest) -> f s <> bifoldMap f g rest)
    ) $ projectW e
  bifoldr f g c e =
    ( foldr (\i a -> bifoldr f g a i) c
    # VariantF.on (SProxy :: SProxy "Embed") (unwrap >>> g <@> c)
    # VariantF.on (SProxy :: SProxy "Note")
      (\(Tuple a rest) -> f a (bifoldr f g c rest))
    ) $ projectW e
  bifoldl f g c e =
    ( foldl (\a i -> bifoldl f g a i) c
    # VariantF.on (SProxy :: SProxy "Embed") (unwrap >>> g c)
    # VariantF.on (SProxy :: SProxy "Note")
      (\(Tuple a rest) -> bifoldl f g (f c a) rest)
    ) $ projectW e
derive newtype instance foldableExpr :: Foldable m => Foldable (Expr m s)
-- (Bi)traversable will allow running computations on the embedded data,
-- e.g. using an error monad to get rid of holes, or using Aff to fill in
-- imports (especially via URL).
instance bitraversableExpr :: Traversable m => Bitraversable (Expr m) where
  bisequence = bisequenceDefault
  bitraverse f g e = map embedW $
    ( ( traverse (bitraverse f g)
    >>> map VariantF.expand
      )
    # VariantF.on (SProxy :: SProxy "Embed")
      (unwrap >>> g >>> map (wrap >>> VariantF.inj (SProxy :: SProxy "Embed")))
    # VariantF.on (SProxy :: SProxy "Note")
      (\(Tuple a rest) -> Tuple <$> f a <*> bitraverse f g rest <#>
        VariantF.inj (SProxy :: SProxy "Note")
      )
    ) $ projectW e
derive newtype instance traversableExpr :: Traversable m => Traversable (Expr m s)

-- A helper to coalesce a tree of annotations into a single annotation on
-- a "real" AST node.
unfurl :: forall m s a. Monoid s =>
  Expr m s a -> Tuple s (VariantF (AllTheThings m ( "Embed" :: CONST a )) (Expr m s a))
unfurl e0 = go mempty e0 where
  go s = projectW >>>
    VariantF.on (SProxy :: SProxy "Note")
      (uncurry go)
      (Tuple s)

coalesce1 :: forall m s a. Monoid s => Expr m s a -> Expr m s a
coalesce1 e = uncurry mkNote $ unfurl e <#>
  VariantF.expand >>> embedW

-- Pris(o)ms of the behemoth
_ExprF :: forall m s a unused f k.
  Row.Cons k (FProxy f) unused (ExprLayerRow m s a) =>
  IsSymbol k => Functor f =>
  SProxy k -> Prism' (Expr m s a) (f (Expr m s a))
_ExprF k = _E (_ExprFPrism k)

-- Convert a prism operating on VariantF ( ... ) Expr to one operating on Expr
_E :: forall f m s a. Functor f =>
  Prism'
    (VariantF (ExprLayerRow m s a) (Expr m s a))
    (f (Expr m s a)) ->
  Prism' (Expr m s a) (f (Expr m s a))
_E p = iso projectW embedW <<< p

type ExprFPrism r f = forall o. Prism' (VariantF r o) (f o)
_ExprFPrism :: forall r unused f k.
  Row.Cons k (FProxy f) unused r =>
  IsSymbol k => Functor f =>
  SProxy k -> ExprFPrism r f
_ExprFPrism k = prism' (VariantF.inj k)
  (VariantF.default Nothing # VariantF.on k Just)

_Expr :: forall m s a unused v k.
  Row.Cons k (CONST v) unused (ExprLayerRow m s a) =>
  IsSymbol k =>
  SProxy k -> Prism' (Expr m s a) v
_Expr k = _E (_ExprPrism k) <<< _Newtype

type ExprPrism r v =
    ExprFPrism
      r
      (ConstF.Const v)

type SimplePrism r v =
  forall o.
    Prism'
      (VariantF r o)
      v

_ExprPrism :: forall r unused v k.
  Row.Cons k (CONST v) unused r =>
  IsSymbol k =>
  SProxy k ->
  ExprPrism r v
_ExprPrism k = _ExprFPrism k

_BinOp :: forall m s a unused k.
  Row.Cons k (FProxy Pair) unused (ExprLayerRow m s a) =>
  IsSymbol k =>
  SProxy k -> Prism' (Expr m s a) (Pair (Expr m s a))
_BinOp k = _E (_BinOpPrism k)

type BinOpPrism r =
    ExprFPrism
      r
      Pair
_BinOpPrism ::
  forall unused k r.
    Row.Cons k (FProxy Pair) unused r =>
    IsSymbol k =>
  SProxy k ->
  BinOpPrism r
_BinOpPrism k = _ExprFPrism k

mkExprF :: forall m s a unused f k.
  Row.Cons k (FProxy f) unused (ExprLayerRow m s a) =>
  IsSymbol k => Functor f =>
  SProxy k -> f (Expr m s a) -> Expr m s a
mkExprF k v = embedW $ VariantF.inj k v

mkExpr :: forall m s a unused v k.
  Row.Cons k (CONST v) unused (ExprLayerRow m s a) =>
  IsSymbol k =>
  SProxy k -> v -> Expr m s a
mkExpr k v = mkExprF k (ConstF.Const v)

mkBinOp :: forall m s a unused k.
  Row.Cons k (FProxy Pair) unused (ExprLayerRow m s a) =>
  IsSymbol k =>
  SProxy k -> Expr m s a -> Expr m s a -> Expr m s a
mkBinOp k l r = mkExprF k
  (Pair l r)

mkConst :: forall m s a. Const -> Expr m s a
mkConst = mkExpr (SProxy :: SProxy "Const")

_Const :: forall r. ExprPrism ( "Const" :: CONST Const | r ) Const
_Const = _ExprPrism (SProxy :: SProxy "Const")

mkVar :: forall m s a. Var -> Expr m s a
mkVar = mkExpr (SProxy :: SProxy "Var")

_Var :: forall r. ExprPrism ( "Var" :: CONST Var | r ) Var
_Var = _ExprPrism (SProxy :: SProxy "Var")

mkLam :: forall m s a. String -> Expr m s a -> Expr m s a -> Expr m s a
mkLam name ty expr = mkExprF (SProxy :: SProxy "Lam")
  (product (Tuple name ty) (Identity expr))

_Lam :: forall r o.
  Prism' (VariantF ( "Lam" :: FProxy BindingBody | r ) o)
  { var :: String, ty :: o, body :: o }
_Lam = _ExprFPrism (SProxy :: SProxy "Lam") <<< _Newtype <<< iso into outof where
  into (Tuple (Tuple var ty) (Identity body)) = { var, ty, body }
  outof { var, ty, body } = (Tuple (Tuple var ty) (Identity body))

mkPi :: forall m s a. String -> Expr m s a -> Expr m s a -> Expr m s a
mkPi name ty expr = mkExprF (SProxy :: SProxy "Pi")
  (product (Tuple name ty) (Identity expr))

_Pi :: forall r o.
  Prism' (VariantF ( "Pi" :: FProxy BindingBody | r ) o)
  { var :: String, ty :: o, body :: o }
_Pi = _ExprFPrism (SProxy :: SProxy "Pi") <<< _Newtype <<< iso into outof where
  into (Tuple (Tuple var ty) (Identity body)) = { var, ty, body }
  outof { var, ty, body } = (Tuple (Tuple var ty) (Identity body))

mkApp :: forall m s a. Expr m s a -> Expr m s a -> Expr m s a
mkApp fn arg = mkExprF (SProxy :: SProxy "App")
  (Pair fn arg)

_App :: forall r o.
  Prism' (VariantF ( "App" :: FProxy Pair | r ) o)
  { fn :: o, arg :: o }
_App = _ExprFPrism (SProxy :: SProxy "App") <<< iso into outof where
  into (Pair fn arg) = { fn, arg }
  outof { fn, arg } = Pair fn arg

mkLet :: forall m s a. String -> Maybe (Expr m s a) -> Expr m s a -> Expr m s a -> Expr m s a
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

mkAnnot :: forall m s a. Expr m s a -> Expr m s a -> Expr m s a
mkAnnot val ty = mkExprF (SProxy :: SProxy "Annot")
  (Pair val ty)

_Annot :: forall r o.
  Prism' (VariantF ( "Annot" :: FProxy Pair | r ) o)
  { value :: o, ty :: o }
_Annot = _ExprFPrism (SProxy :: SProxy "Annot") <<< iso into outof where
  into (Pair value ty) = { value, ty }
  outof { value, ty } = Pair value ty

mkBool :: forall m s a. Expr m s a
mkBool = mkExpr (SProxy :: SProxy "Bool") unit

_Bool :: forall r. ExprPrism ( "Bool" :: UNIT | r ) Unit
_Bool = _ExprPrism (SProxy :: SProxy "Bool")

mkBoolLit :: forall m s a. Boolean -> Expr m s a
mkBoolLit = mkExpr (SProxy :: SProxy "BoolLit")

_BoolLit :: forall r. ExprPrism ( "BoolLit" :: CONST Boolean | r ) Boolean
_BoolLit = _ExprPrism (SProxy :: SProxy "BoolLit")

_BoolLit_True :: forall r. SimplePrism ( "BoolLit" :: CONST Boolean | r ) Unit
_BoolLit_True = _BoolLit <<< _Newtype <<< only true

_BoolLit_False :: forall r. SimplePrism ( "BoolLit" :: CONST Boolean | r ) Unit
_BoolLit_False = _BoolLit <<< _Newtype <<< only false

mkBoolAnd :: forall m s a. Expr m s a -> Expr m s a -> Expr m s a
mkBoolAnd = mkBinOp (SProxy :: SProxy "BoolAnd")

_BoolAnd :: forall r. BinOpPrism ( "BoolAnd" :: FProxy Pair | r )
_BoolAnd = _BinOpPrism (SProxy :: SProxy "BoolAnd")

mkBoolOr :: forall m s a. Expr m s a -> Expr m s a -> Expr m s a
mkBoolOr = mkBinOp (SProxy :: SProxy "BoolOr")

_BoolOr :: forall r. BinOpPrism ( "BoolOr" :: FProxy Pair | r )
_BoolOr = _BinOpPrism (SProxy :: SProxy "BoolOr")

mkBoolEQ :: forall m s a. Expr m s a -> Expr m s a -> Expr m s a
mkBoolEQ = mkBinOp (SProxy :: SProxy "BoolEQ")

_BoolEQ :: forall r. BinOpPrism ( "BoolEQ" :: FProxy Pair | r )
_BoolEQ = _BinOpPrism (SProxy :: SProxy "BoolEQ")

mkBoolNE :: forall m s a. Expr m s a -> Expr m s a -> Expr m s a
mkBoolNE = mkBinOp (SProxy :: SProxy "BoolNE")

_BoolNE :: forall r. BinOpPrism ( "BoolNE" :: FProxy Pair | r )
_BoolNE = _BinOpPrism (SProxy :: SProxy "BoolNE")

mkBoolIf :: forall m s a. Expr m s a -> Expr m s a -> Expr m s a -> Expr m s a
mkBoolIf cond t f = mkExprF (SProxy :: SProxy "BoolIf")
  (Triplet cond t f)

_BoolIf :: forall r. ExprFPrism ( "BoolIf" :: FProxy Triplet | r ) Triplet
_BoolIf = _ExprFPrism (SProxy :: SProxy "BoolIf")

mkNatural :: forall m s a. Expr m s a
mkNatural = mkExpr (SProxy :: SProxy "Natural") unit

_Natural :: forall r. ExprPrism ( "Natural" :: UNIT | r ) Unit
_Natural = _ExprPrism (SProxy :: SProxy "Natural")

mkNaturalLit :: forall m s a. Natural -> Expr m s a
mkNaturalLit = mkExpr (SProxy :: SProxy "NaturalLit")

_NaturalLit :: forall r. ExprPrism ( "NaturalLit" :: CONST Natural | r ) Natural
_NaturalLit = _ExprPrism (SProxy :: SProxy "NaturalLit")

_NaturalLit_0 :: forall r. SimplePrism ( "NaturalLit" :: CONST Natural | r ) Unit
_NaturalLit_0 = _NaturalLit <<< _Newtype <<< only zero

_NaturalLit_1 :: forall r. SimplePrism ( "NaturalLit" :: CONST Natural | r ) Unit
_NaturalLit_1 = _NaturalLit <<< _Newtype <<< only one

mkNaturalFold :: forall m s a. Expr m s a
mkNaturalFold = mkExpr (SProxy :: SProxy "NaturalFold") unit

_NaturalFold :: forall r. ExprPrism ( "NaturalFold" :: UNIT | r ) Unit
_NaturalFold = _ExprPrism (SProxy :: SProxy "NaturalFold")

mkNaturalBuild :: forall m s a. Expr m s a
mkNaturalBuild = mkExpr (SProxy :: SProxy "NaturalBuild") unit

_NaturalBuild :: forall r. ExprPrism ( "NaturalBuild" :: UNIT | r ) Unit
_NaturalBuild = _ExprPrism (SProxy :: SProxy "NaturalBuild")

mkNaturalIsZero :: forall m s a. Expr m s a
mkNaturalIsZero = mkExpr (SProxy :: SProxy "NaturalIsZero") unit

_NaturalIsZero :: forall r. ExprPrism ( "NaturalIsZero" :: UNIT | r ) Unit
_NaturalIsZero = _ExprPrism (SProxy :: SProxy "NaturalIsZero")

mkNaturalEven :: forall m s a. Expr m s a
mkNaturalEven = mkExpr (SProxy :: SProxy "NaturalEven") unit

_NaturalEven :: forall r. ExprPrism ( "NaturalEven" :: UNIT | r ) Unit
_NaturalEven = _ExprPrism (SProxy :: SProxy "NaturalEven")

mkNaturalOdd :: forall m s a. Expr m s a
mkNaturalOdd = mkExpr (SProxy :: SProxy "NaturalOdd") unit

_NaturalOdd :: forall r. ExprPrism ( "NaturalOdd" :: UNIT | r ) Unit
_NaturalOdd = _ExprPrism (SProxy :: SProxy "NaturalOdd")

mkNaturalToInteger :: forall m s a. Expr m s a
mkNaturalToInteger = mkExpr (SProxy :: SProxy "NaturalToInteger") unit

_NaturalToInteger :: forall r. ExprPrism ( "NaturalToInteger" :: UNIT | r ) Unit
_NaturalToInteger = _ExprPrism (SProxy :: SProxy "NaturalToInteger")

mkNaturalShow :: forall m s a. Expr m s a
mkNaturalShow = mkExpr (SProxy :: SProxy "NaturalShow") unit

_NaturalShow :: forall r. ExprPrism ( "NaturalShow" :: UNIT | r ) Unit
_NaturalShow = _ExprPrism (SProxy :: SProxy "NaturalShow")

mkNaturalPlus :: forall m s a. Expr m s a -> Expr m s a -> Expr m s a
mkNaturalPlus = mkBinOp (SProxy :: SProxy "NaturalPlus")

_NaturalPlus :: forall r. BinOpPrism ( "NaturalPlus" :: FProxy Pair | r )
_NaturalPlus = _BinOpPrism (SProxy :: SProxy "NaturalPlus")

mkNaturalTimes :: forall m s a. Expr m s a -> Expr m s a -> Expr m s a
mkNaturalTimes = mkBinOp (SProxy :: SProxy "NaturalTimes")

_NaturalTimes :: forall r. BinOpPrism ( "NaturalTimes" :: FProxy Pair | r )
_NaturalTimes = _BinOpPrism (SProxy :: SProxy "NaturalTimes")

mkInteger :: forall m s a. Expr m s a
mkInteger = mkExpr (SProxy :: SProxy "Integer") unit

_Integer :: forall r. ExprPrism ( "Integer" :: UNIT | r ) Unit
_Integer = _ExprPrism (SProxy :: SProxy "Integer")

mkIntegerLit :: forall m s a. Int -> Expr m s a
mkIntegerLit = mkExpr (SProxy :: SProxy "IntegerLit")

_IntegerLit :: forall r. ExprPrism ( "IntegerLit" :: CONST Int | r ) Int
_IntegerLit = _ExprPrism (SProxy :: SProxy "IntegerLit")

mkIntegerShow :: forall m s a. Expr m s a
mkIntegerShow = mkExpr (SProxy :: SProxy "IntegerShow") unit

_IntegerShow :: forall r. ExprPrism ( "IntegerShow" :: UNIT | r ) Unit
_IntegerShow = _ExprPrism (SProxy :: SProxy "IntegerShow")

mkIntegerToDouble :: forall m s a. Expr m s a
mkIntegerToDouble = mkExpr (SProxy :: SProxy "IntegerToDouble") unit

_IntegerToDouble :: forall r. ExprPrism ( "IntegerToDouble" :: UNIT | r ) Unit
_IntegerToDouble = _ExprPrism (SProxy :: SProxy "IntegerToDouble")

mkDouble :: forall m s a. Expr m s a
mkDouble = mkExpr (SProxy :: SProxy "Double") unit

_Double :: forall r. ExprPrism ( "Double" :: UNIT | r ) Unit
_Double = _ExprPrism (SProxy :: SProxy "Double")

mkDoubleLit :: forall m s a. Number -> Expr m s a
mkDoubleLit = mkExpr (SProxy :: SProxy "DoubleLit")

_DoubleLit :: forall r. ExprPrism ( "DoubleLit" :: CONST Number | r ) Number
_DoubleLit = _ExprPrism (SProxy :: SProxy "DoubleLit")

mkDoubleShow :: forall m s a. Expr m s a
mkDoubleShow = mkExpr (SProxy :: SProxy "DoubleShow") unit

_DoubleShow :: forall r. ExprPrism ( "DoubleShow" :: UNIT | r ) Unit
_DoubleShow = _ExprPrism (SProxy :: SProxy "DoubleShow")

mkText :: forall m s a. Expr m s a
mkText = mkExpr (SProxy :: SProxy "Text") unit

_Text :: forall r. ExprPrism ( "Text" :: UNIT | r ) Unit
_Text = _ExprPrism (SProxy :: SProxy "Text")

mkTextLit :: forall m s a. TextLitF (Expr m s a) -> Expr m s a
mkTextLit = mkExprF (SProxy :: SProxy "TextLit")

_TextLit :: forall r. ExprFPrism ( "TextLit" :: FProxy TextLitF | r ) TextLitF
_TextLit = _ExprFPrism (SProxy :: SProxy "TextLit")

_TextLit_empty :: forall r o. Prism' (VariantF ( "TextLit" :: FProxy TextLitF | r ) o) Unit
_TextLit_empty = _TextLit <<< prism' (const (TextLit ""))
  case _ of
    TextLit "" -> Just unit
    _ -> Nothing

mkTextAppend :: forall m s a. Expr m s a -> Expr m s a -> Expr m s a
mkTextAppend = mkBinOp (SProxy :: SProxy "TextAppend")

_TextAppend :: forall r. BinOpPrism ( "TextAppend" :: FProxy Pair | r )
_TextAppend = _BinOpPrism (SProxy :: SProxy "TextAppend")

mkList :: forall m s a. Expr m s a
mkList = mkExpr (SProxy :: SProxy "List") unit

_List :: forall r. ExprPrism ( "List" :: UNIT | r ) Unit
_List = _ExprPrism (SProxy :: SProxy "List")

mkListLit :: forall m s a. Maybe (Expr m s a) -> Array (Expr m s a) -> Expr m s a
mkListLit ty lit = mkExprF (SProxy :: SProxy "ListLit")
  (product ty lit)

_ListLit :: forall r o.
  Prism' (VariantF ( "ListLit" :: FProxy (Product Maybe Array) | r ) o)
  { ty :: Maybe o, values :: Array o }
_ListLit = _ExprFPrism (SProxy :: SProxy "ListLit") <<< _Newtype <<< iso into outof where
  into (Tuple ty values) = { ty, values }
  outof { ty, values } = Tuple ty values

mkListAppend :: forall m s a. Expr m s a -> Expr m s a -> Expr m s a
mkListAppend = mkBinOp (SProxy :: SProxy "ListAppend")

_ListAppend :: forall r. BinOpPrism ( "ListAppend" :: FProxy Pair | r )
_ListAppend = _BinOpPrism (SProxy :: SProxy "ListAppend")

mkListFold :: forall m s a. Expr m s a
mkListFold = mkExpr (SProxy :: SProxy "ListFold") unit

_ListFold :: forall r. ExprPrism ( "ListFold" :: UNIT | r ) Unit
_ListFold = _ExprPrism (SProxy :: SProxy "ListFold")

mkListBuild :: forall m s a. Expr m s a
mkListBuild = mkExpr (SProxy :: SProxy "ListBuild") unit

_ListBuild :: forall r. ExprPrism ( "ListBuild" :: UNIT | r ) Unit
_ListBuild = _ExprPrism (SProxy :: SProxy "ListBuild")

mkListLength :: forall m s a. Expr m s a
mkListLength = mkExpr (SProxy :: SProxy "ListLength") unit

_ListLength :: forall r. ExprPrism ( "ListLength" :: UNIT | r ) Unit
_ListLength = _ExprPrism (SProxy :: SProxy "ListLength")

mkListHead :: forall m s a. Expr m s a
mkListHead = mkExpr (SProxy :: SProxy "ListHead") unit

_ListHead :: forall r. ExprPrism ( "ListHead" :: UNIT | r ) Unit
_ListHead = _ExprPrism (SProxy :: SProxy "ListHead")

mkListLast :: forall m s a. Expr m s a
mkListLast = mkExpr (SProxy :: SProxy "ListLast") unit

_ListLast :: forall r. ExprPrism ( "ListLast" :: UNIT | r ) Unit
_ListLast = _ExprPrism (SProxy :: SProxy "ListLast")

mkListIndexed :: forall m s a. Expr m s a
mkListIndexed = mkExpr (SProxy :: SProxy "ListIndexed") unit

_ListIndexed :: forall r. ExprPrism ( "ListIndexed" :: UNIT | r ) Unit
_ListIndexed = _ExprPrism (SProxy :: SProxy "ListIndexed")

mkListReverse :: forall m s a. Expr m s a
mkListReverse = mkExpr (SProxy :: SProxy "ListReverse") unit

_ListReverse :: forall r. ExprPrism ( "ListReverse" :: UNIT | r ) Unit
_ListReverse = _ExprPrism (SProxy :: SProxy "ListReverse")

mkOptional :: forall m s a. Expr m s a
mkOptional = mkExpr (SProxy :: SProxy "Optional") unit

_Optional :: forall r. ExprPrism ( "Optional" :: UNIT | r ) Unit
_Optional = _ExprPrism (SProxy :: SProxy "Optional")

mkOptionalLit :: forall m s a. Expr m s a -> Maybe (Expr m s a) -> Expr m s a
mkOptionalLit ty lit = mkExprF (SProxy :: SProxy "OptionalLit")
  (product (Identity ty) lit)

_OptionalLit :: forall r o.
  Prism' (VariantF ( "OptionalLit" :: FProxy (Product Identity Maybe) | r ) o)
  { ty :: o, value :: Maybe o }
_OptionalLit = _ExprFPrism (SProxy :: SProxy "OptionalLit") <<< _Newtype <<< iso into outof where
  into (Tuple (Identity ty) value) = { ty, value }
  outof { ty, value } = Tuple (Identity ty) value

mkOptionalFold :: forall m s a. Expr m s a
mkOptionalFold = mkExpr (SProxy :: SProxy "OptionalFold") unit

_OptionalFold :: forall r. ExprPrism ( "OptionalFold" :: UNIT | r ) Unit
_OptionalFold = _ExprPrism (SProxy :: SProxy "OptionalFold")

mkOptionalBuild :: forall m s a. Expr m s a
mkOptionalBuild = mkExpr (SProxy :: SProxy "OptionalBuild") unit

_OptionalBuild :: forall r. ExprPrism ( "OptionalBuild" :: UNIT | r ) Unit
_OptionalBuild = _ExprPrism (SProxy :: SProxy "OptionalBuild")

mkRecord :: forall m s a. Functor m => m (Expr m s a) -> Expr m s a
mkRecord = mkExprF (SProxy :: SProxy "Record")

_Record :: forall r m. Functor m => ExprFPrism
  ( "Record" :: FProxy m | r ) m
_Record = _ExprFPrism (SProxy :: SProxy "Record")

_Record_empty :: forall r o m. StrMapIsh m =>
  Prism' (VariantF ( "Record" :: FProxy m | r ) o) Unit
_Record_empty = _Record <<< StrMapIsh._Empty

mkRecordLit :: forall s a m. Functor m => m (Expr m s a) -> Expr m s a
mkRecordLit = mkExprF (SProxy :: SProxy "RecordLit")

_RecordLit :: forall r m. Functor m => ExprFPrism
  ( "RecordLit" :: FProxy m | r ) m
_RecordLit = _ExprFPrism (SProxy :: SProxy "RecordLit")

_RecordLit_empty :: forall r o m. StrMapIsh m =>
  Prism' (VariantF ( "RecordLit" :: FProxy m | r ) o) Unit
_RecordLit_empty = _RecordLit <<< StrMapIsh._Empty

mkUnion :: forall m s a. Functor m => m (Expr m s a) -> Expr m s a
mkUnion = mkExprF (SProxy :: SProxy "Union")

_Union :: forall r m. Functor m => ExprFPrism ( "Union" :: FProxy m | r ) m
_Union = _ExprFPrism (SProxy :: SProxy "Union")

_Union_empty :: forall r o m. StrMapIsh m =>
  Prism' (VariantF ( "Union" :: FProxy m | r ) o) Unit
_Union_empty = _Union <<< StrMapIsh._Empty

mkUnionLit :: forall m s a. Functor m => String -> Expr m s a -> m (Expr m s a) -> Expr m s a
mkUnionLit name value others = mkExprF (SProxy :: SProxy "UnionLit")
  (product (Tuple name value) others)

_UnionLit :: forall r o m. Functor m => Prism'
  (VariantF ( "UnionLit" :: FProxy (Product (Tuple String) m) | r ) o)
  { label :: String, value :: o, tys :: m o }
_UnionLit = _ExprFPrism (SProxy :: SProxy "UnionLit") <<< _Newtype <<< iso into outof where
  into (Tuple (Tuple label value) tys) = { label, value, tys }
  outof { label, value, tys } = Tuple (Tuple label value) tys

mkCombine :: forall m s a. Expr m s a -> Expr m s a -> Expr m s a
mkCombine = mkBinOp (SProxy :: SProxy "Combine")

_Combine :: forall r. BinOpPrism ( "Combine" :: FProxy Pair | r )
_Combine = _BinOpPrism (SProxy :: SProxy "Combine")

mkCombineTypes :: forall m s a. Expr m s a -> Expr m s a -> Expr m s a
mkCombineTypes = mkBinOp (SProxy :: SProxy "CombineTypes")

_CombineTypes :: forall r. BinOpPrism ( "CombineTypes" :: FProxy Pair | r )
_CombineTypes = _BinOpPrism (SProxy :: SProxy "CombineTypes")

mkPrefer :: forall m s a. Expr m s a -> Expr m s a -> Expr m s a
mkPrefer = mkBinOp (SProxy :: SProxy "Prefer")

_Prefer :: forall r. BinOpPrism ( "Prefer" :: FProxy Pair | r )
_Prefer = _BinOpPrism (SProxy :: SProxy "Prefer")

mkMerge :: forall m s a. Expr m s a -> Expr m s a -> Maybe (Expr m s a) -> Expr m s a
mkMerge x y t = mkExprF (SProxy :: SProxy "Merge")
  (MergeF x y t)

_Merge :: forall r. ExprFPrism ( "Merge" :: FProxy MergeF | r ) MergeF
_Merge = _ExprFPrism (SProxy :: SProxy "Merge")

mkConstructors :: forall m s a. Expr m s a -> Expr m s a
mkConstructors = mkExprF (SProxy :: SProxy "Constructors") <<< Identity

_Constructors :: forall r o.
  Prism' (VariantF ( "Constructors" :: FProxy Identity | r ) o) o
_Constructors = _ExprFPrism (SProxy :: SProxy "Constructors") <<< _Newtype

mkField :: forall m s a. Expr m s a -> String -> Expr m s a
mkField expr field = mkExprF (SProxy :: SProxy "Field")
  (Tuple field expr)

_Field :: forall r o. Prism'
  (VariantF ( "Field" :: FProxy (Tuple String) | r ) o)
  (Tuple o String)
_Field = _ExprFPrism (SProxy :: SProxy "Field") <<< iso swap swap

mkProject :: forall m s a. Expr m s a -> Set String -> Expr m s a
mkProject expr fields = mkExprF (SProxy :: SProxy "Project")
  (Tuple fields expr)

_Project :: forall r o. Prism'
  (VariantF ( "Project" :: FProxy (Tuple (Set String)) | r ) o)
  (Tuple o (Set String))
_Project = _ExprFPrism (SProxy :: SProxy "Project") <<< iso swap swap

mkNote :: forall m s a. s -> Expr m s a -> Expr m s a
mkNote note expr = mkExprF (SProxy :: SProxy "Note")
  (Tuple note expr)

_Note :: forall s r. ExprFPrism ( "Note" :: FProxy (Tuple s) | r ) (Tuple s)
_Note = _ExprFPrism (SProxy :: SProxy "Note")

mkImportAlt :: forall m s a. Expr m s a -> Expr m s a -> Expr m s a
mkImportAlt = mkBinOp (SProxy :: SProxy "ImportAlt")

_ImportAlt :: forall r. BinOpPrism ( "ImportAlt" :: FProxy Pair | r )
_ImportAlt = _BinOpPrism (SProxy :: SProxy "ImportAlt")

mkEmbed :: forall m s a. a -> Expr m s a
mkEmbed = pure

_Embed :: forall a r. ExprPrism ( "Embed" :: CONST a | r ) a
_Embed = _ExprPrism (SProxy :: SProxy "Embed")

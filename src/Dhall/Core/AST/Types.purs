module Dhall.Core.AST.Types where

import Prelude

import Control.Monad.Free (Free, hoistFree)
import Data.Bifoldable (class Bifoldable, bifoldMap, bifoldl, bifoldr)
import Data.Bifunctor (class Bifunctor, lmap)
import Data.Bitraversable (class Bitraversable, bitraverse, bisequenceDefault)
import Data.Const as ConstF
import Data.Either (Either(..), either)
import Data.Eq (class Eq1, eq1)
import Data.Foldable (class Foldable, foldMap, foldl, foldr)
import Data.FoldableWithIndex (class FoldableWithIndex, foldMapWithIndex)
import Data.Functor.Product (Product(..))
import Data.Functor.Variant (VariantF)
import Data.Functor.Variant as VariantF
import Data.Identity (Identity(..))
import Data.Maybe (Maybe(..))
import Data.Natural (Natural)
import Data.Newtype (class Newtype, un, unwrap, wrap)
import Data.Set (Set)
import Data.String (joinWith)
import Data.Symbol (class IsSymbol, SProxy(..))
import Data.Traversable (class Traversable, traverse)
import Data.Tuple (Tuple(..))
import Data.Variant.Internal (FProxy)
import Dhall.Core.AST.Types.Basics (BindingBody(..), CONST, LetF(..), MergeF(..), Pair(..), TextLitF(..), Triplet(..), UNIT)
import Matryoshka (class Corecursive, class Recursive, cata, embed, project)
import Prim.Row as Row
import Type.Row (type (+))

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
        (\(BindingBody n t b) -> "(mkLam " <> show n <> t <> b <> ")")
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
        (\(BindingBody n t b) -> "(mkPi " <> n <> t <> b <> ")")
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
derive newtype instance foldableERVF :: Foldable m => Foldable (ExprRowVF m s a)
derive newtype instance traversableERVF :: Traversable m => Traversable (ExprRowVF m s a)
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

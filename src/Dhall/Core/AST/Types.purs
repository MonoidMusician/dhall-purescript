module Dhall.Core.AST.Types where

import Prelude

import Control.Comonad (extract)
import Control.Monad.Free (Free, hoistFree)
import Data.Bifunctor (class Bifunctor, lmap)
import Data.Const as ConstF
import Data.Either (Either(..), either)
import Data.Eq (class Eq1, eq1)
import Data.Foldable (class Foldable, fold, foldl, foldr)
import Data.FoldableWithIndex (class FoldableWithIndex, foldMapWithIndex)
import Data.Functor.App (App(..))
import Data.Functor.Product (Product(..), bihoistProduct)
import Data.Functor.Variant (VariantF)
import Data.Functor.Variant as VariantF
import Data.FunctorWithIndex (class FunctorWithIndex, mapWithIndex)
import Data.Identity (Identity(..))
import Data.Maybe (Maybe(..))
import Data.Natural (Natural)
import Data.Newtype (class Newtype, un, unwrap, wrap, over)
import Data.Ord (class Ord1, compare1)
import Data.String (joinWith)
import Data.Symbol (class IsSymbol, SProxy(..))
import Data.Traversable (class Traversable, sequence)
import Data.TraversableWithIndex (class TraversableWithIndex)
import Data.Tuple (Tuple(..))
import Data.Variant (Variant)
import Data.Variant.Internal (FProxy)
import Dhall.Core.AST.Types.Basics (BindingBody(..), BindingBody', BindingBodyI, CONST, LetF(..), LetF', LetFI, MergeF(..), MergeF', MergeFI, Pair(..), Pair', PairI, TextLitF(..), TextLitF', TextLitFI, Triplet(..), Triplet', TripletI, UNIT, VOID)
import Dhall.Core.Zippers (class Container, class ContainerI, Array', ArrayI, Identity', IdentityI, Maybe', MaybeI, Product', ProductI, Tuple', TupleI, _contextZF, downZFV, ixFV, mapWithIndexV, upZFV, (:<-:))
import Dhall.Core.Zippers.Merge (class Merge)
import Dhall.Core.Zippers.Recursive (ZRec, Indices)
import Matryoshka (class Corecursive, class Recursive, cata, embed, project)
import Prim.Row as Row
import Type.Row (type (+))

-- This file defines the Expr type by its cases, and gives instances, etc.

-- copied from dhall-haskell
data Const = Type | Kind
derive instance eqConst :: Eq Const
derive instance ordConst :: Ord Const

-- copied from dhall-haskell
data Var = V String Int
derive instance eqVar :: Eq Var
derive instance ordVar :: Ord Var

-- Constant (non-recursive) literal types; the base of the AST, essentially
type Literals (m :: Type -> Type) vs =
  ( "BoolLit" :: CONST Boolean
  , "NaturalLit" :: CONST Natural
  , "IntegerLit" :: CONST Int
  , "DoubleLit" :: CONST Number
  | vs
  )

type Literals' (m :: Type -> Type) (m' :: Type -> Type) vs =
  ( "BoolLit" :: VOID
  , "NaturalLit" :: VOID
  , "IntegerLit" :: VOID
  , "DoubleLit" :: VOID
  | vs
  )

type LiteralsI vs =
  ( "BoolLit" :: Void
  , "NaturalLit" :: Void
  , "IntegerLit" :: Void
  , "DoubleLit" :: Void
  | vs
  )

-- Other kinds of literals that _are_ recursive
type Literals2 (m :: Type -> Type) v =
  ( "TextLit" :: FProxy TextLitF
  , "ListLit" :: FProxy (Product Maybe Array)
  , "OptionalLit" :: FProxy (Product Identity Maybe)
  , "Some" :: FProxy Identity
  , "None" :: CONST Unit
  , "RecordLit" :: FProxy m
  , "UnionLit" :: FProxy (Product (Tuple String) m)
  | v
  )

type Literals2' (m :: Type -> Type) (m' :: Type -> Type) v =
  ( "TextLit" :: FProxy TextLitF'
  , "ListLit" :: FProxy (Product' Maybe Maybe' Array Array')
  , "OptionalLit" :: FProxy (Product' Identity Identity' Maybe Maybe')
  , "Some" :: FProxy Identity'
  , "None" :: VOID
  , "RecordLit" :: FProxy m'
  , "UnionLit" :: FProxy (Product' (Tuple String) (Tuple' String) m m')
  | v
  )

type Literals2I v =
  ( "TextLit" :: TextLitFI
  , "ListLit" :: ProductI MaybeI ArrayI
  , "OptionalLit" :: ProductI IdentityI MaybeI
  , "Some" :: IdentityI
  , "None" :: Void
  , "RecordLit" :: String
  , "UnionLit" :: ProductI (TupleI String) String
  | v
  )

-- The types that are essentially axiomatically added
type BuiltinTypes (m :: Type -> Type) vs =
  ( "Bool" :: UNIT
  , "Natural" :: UNIT
  , "Integer" :: UNIT
  , "Double" :: UNIT
  , "Text" :: UNIT
  , "List" :: UNIT
  , "Optional" :: UNIT
  , "Const" :: CONST Const
  | vs
  )

type BuiltinTypes' (m :: Type -> Type) (m' :: Type -> Type) vs =
  ( "Bool" :: VOID
  , "Natural" :: VOID
  , "Integer" :: VOID
  , "Double" :: VOID
  , "Text" :: VOID
  , "List" :: VOID
  , "Optional" :: VOID
  , "Const" :: VOID
  | vs
  )

type BuiltinTypesI vs =
  ( "Bool" :: Void
  , "Natural" :: Void
  , "Integer" :: Void
  , "Double" :: Void
  , "Text" :: Void
  , "List" :: Void
  , "Optional" :: Void
  , "Const" :: Void
  | vs
  )

-- Record and union types (which are recursive)
type BuiltinTypes2 (m :: Type -> Type) v =
  ( "Record" :: FProxy m
  , "Union" :: FProxy m
  | v
  )

type BuiltinTypes2' (m :: Type -> Type) (m' :: Type -> Type) v =
  ( "Record" :: FProxy m'
  , "Union" :: FProxy m'
  | v
  )

type BuiltinTypes2I v =
  ( "Record" :: String
  , "Union" :: String
  | v
  )

-- Builtin functions, also essentially axioms
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

type BuiltinFuncs' (m :: Type -> Type) (m' :: Type -> Type) vs =
  ( "NaturalFold" :: VOID
  , "NaturalBuild" :: VOID
  , "NaturalIsZero" :: VOID
  , "NaturalEven" :: VOID
  , "NaturalOdd" :: VOID
  , "NaturalToInteger" :: VOID
  , "NaturalShow" :: VOID
  , "IntegerShow" :: VOID
  , "IntegerToDouble" :: VOID
  , "DoubleShow" :: VOID
  , "ListBuild" :: VOID
  , "ListFold" :: VOID
  , "ListLength" :: VOID
  , "ListHead" :: VOID
  , "ListLast" :: VOID
  , "ListIndexed" :: VOID
  , "ListReverse" :: VOID
  , "OptionalFold" :: VOID
  , "OptionalBuild" :: VOID
  | vs
  )

type BuiltinFuncsI vs =
  ( "NaturalFold" :: Void
  , "NaturalBuild" :: Void
  , "NaturalIsZero" :: Void
  , "NaturalEven" :: Void
  , "NaturalOdd" :: Void
  , "NaturalToInteger" :: Void
  , "NaturalShow" :: Void
  , "IntegerShow" :: Void
  , "IntegerToDouble" :: Void
  , "DoubleShow" :: Void
  , "ListBuild" :: Void
  , "ListFold" :: Void
  , "ListLength" :: Void
  , "ListHead" :: Void
  , "ListLast" :: Void
  , "ListIndexed" :: Void
  , "ListReverse" :: Void
  , "OptionalFold" :: Void
  , "OptionalBuild" :: Void
  | vs
  )

-- And binary operations
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

type BuiltinBinOps' (m :: Type -> Type) (m' :: Type -> Type) vs =
  ( "BoolAnd" :: FProxy Pair'
  , "BoolOr" :: FProxy Pair'
  , "BoolEQ" :: FProxy Pair'
  , "BoolNE" :: FProxy Pair'
  , "NaturalPlus" :: FProxy Pair'
  , "NaturalTimes" :: FProxy Pair'
  , "TextAppend" :: FProxy Pair'
  , "ListAppend" :: FProxy Pair'
  , "Combine" :: FProxy Pair'
  , "CombineTypes" :: FProxy Pair'
  , "Prefer" :: FProxy Pair'
  , "ImportAlt" :: FProxy Pair'
  | vs
  )

type BuiltinBinOpsI vs =
  ( "BoolAnd" :: PairI
  , "BoolOr" :: PairI
  , "BoolEQ" :: PairI
  , "BoolNE" :: PairI
  , "NaturalPlus" :: PairI
  , "NaturalTimes" :: PairI
  , "TextAppend" :: PairI
  , "ListAppend" :: PairI
  , "Combine" :: PairI
  , "CombineTypes" :: PairI
  , "Prefer" :: PairI
  , "ImportAlt" :: PairI
  | vs
  )

-- All builtin operations with their own syntax
type BuiltinOps (m :: Type -> Type) v = BuiltinBinOps m
  ( "BoolIf" :: FProxy (Triplet)
  , "Field" :: FProxy (Tuple String)
  , "Project" :: FProxy (Tuple (App m Unit))
  , "Merge" :: FProxy (MergeF)
  , "Constructors" :: FProxy Identity
  | v
  )

type BuiltinOps' (m :: Type -> Type) (m' :: Type -> Type) v = BuiltinBinOps' m m'
  ( "BoolIf" :: FProxy (Triplet')
  , "Field" :: FProxy (Tuple' String)
  , "Project" :: FProxy (Tuple' (App m Unit))
  , "Merge" :: FProxy (MergeF')
  , "Constructors" :: FProxy Identity'
  | v
  )

type BuiltinOpsI v = BuiltinBinOpsI
  ( "BoolIf" :: TripletI
  , "Field" :: TupleI String
  , "Project" :: Unit
  , "Merge" :: MergeFI
  , "Constructors" :: IdentityI
  | v
  )

type Variable (m :: Type -> Type) v =
  ( "Lam" :: FProxy BindingBody
  , "Pi" :: FProxy BindingBody
  , "Let" :: FProxy LetF
  , "Var" :: CONST Var
  | v
  )

type Variable' (m :: Type -> Type) (m' :: Type -> Type) v =
  ( "Lam" :: FProxy (BindingBody')
  , "Pi" :: FProxy (BindingBody')
  , "Let" :: FProxy LetF'
  , "Var" :: VOID
  | v
  )

type VariableI v =
  ( "Lam" :: BindingBodyI
  , "Pi" :: BindingBodyI
  , "Let" :: LetFI
  , "Var" :: Void
  | v
  )

-- Other things that have special/fundamental syntax
type Syntax (m :: Type -> Type) v =
  ( "App" :: FProxy Pair
  , "Annot" :: FProxy Pair
  | v
  )

type Syntax' (m :: Type -> Type) (m' :: Type -> Type) v =
  ( "App" :: FProxy Pair'
  , "Annot" :: FProxy Pair'
  | v
  )

type SyntaxI v =
  ( "App" :: PairI
  , "Annot" :: PairI
  | v
  )

-- Non-recursive items
type SimpleThings m vs = Literals m + BuiltinTypes m + BuiltinFuncs m + vs
type SimpleThings' m m' vs = Literals' m m' + BuiltinTypes' m m' + BuiltinFuncs' m m' + vs
type SimpleThingsI vs = LiteralsI + BuiltinTypesI + BuiltinFuncsI + vs

-- Recursive items
type FunctorThings m v = Literals2 m + BuiltinTypes2 m + BuiltinOps m + Syntax m + Variable m + v
type FunctorThings' m m' v = Literals2' m m' + BuiltinTypes2' m m' + BuiltinOps' m m' + Syntax' m m' + Variable' m m' + v
type FunctorThingsI v = Literals2I + BuiltinTypes2I + BuiltinOpsI + SyntaxI + VariableI + v

-- Both together
type AllTheThings m v = SimpleThings m + FunctorThings m + v
type AllTheThings' m m' v = SimpleThings' m m' + FunctorThings' m m' + v
type AllTheThingsI v = SimpleThingsI + FunctorThingsI + v

-- A layer of Expr (within Free) is AllTheThings
-- No Note constructor anymore!
type ExprRow m = AllTheThings m ()
type ExprRow' m m' = AllTheThings' m m' ()
type ExprRowI = AllTheThingsI ()
-- While a layer (within Mu, not Free) must also include the `a` parameter
-- via the Embed constructor
type ExprLayerRow m a =
  AllTheThings m
    ( "Embed" :: CONST a
    )
type ExprLayerRow' m m' a =
  AllTheThings' m m'
    ( "Embed" :: VOID
    )
type ExprLayerRowI =
  AllTheThingsI
    ( "Embed" :: Void
    )
-- The same, as a variant
-- (This has a newtype in ExprRowVF)
type ExprLayerF m a = VariantF (ExprLayerRow m a)
type ExprLayerF' m m' a = VariantF (ExprLayerRow' m m' a)
type ExprLayerFI = Variant ExprLayerRowI
-- The same, but applied to Expr (this is isomorphic to Expr itself)
type ExprLayer m a = (ExprLayerF m a) (Expr m a)

-- Expr itself, the type of AST nodes.
--
-- It is represented via a Free monad over the VariantF of the rows enumerated
-- above. The VariantF thus gives the main syntax, where `m` specifies the
-- functor to use for records and unions and the like, and `a` is additional
-- terminals (e.g. imports), which can be mapped and applied and traversed over.
newtype Expr m a = Expr (Free (VariantF (ExprRow m)) a)
derive instance newtypeExpr :: Newtype (Expr m a) _

type Expr' m m' a = ZRec (ExprRowVF' m m' a) (Expr m a)
type ExprI = Indices ExprRowVFI

-- Give Expr its own Recursive instance with ExprRowVF (a newtype of ExprLayerF)
instance recursiveExpr :: Recursive (Expr m a) (ExprRowVF m a) where
  project = unwrap >>> project >>> map Expr >>> unwrap >>> either
    (wrap >>> VariantF.inj (SProxy :: SProxy "Embed"))
    VariantF.expand >>> ERVF

instance corecursiveExpr :: Corecursive (Expr m a) (ExprRowVF m a) where
  embed = wrap <<< embed <<< map (un Expr) <<< wrap <<<
    VariantF.on (SProxy :: SProxy "Embed") (Left <<< unwrap) Right <<< un ERVF

-- Project and unwrap the ExprRowVF newtype, to allow instant handling of the
-- cases via VariantF's api.
projectW :: forall m a. Expr m a -> ExprLayer m a
projectW = project >>> unwrap

embedW :: forall m a. ExprLayer m a -> Expr m a
embedW = embed <<< wrap

-- Really ugly showing for Expr
instance showExpr :: (TraversableWithIndex String m, Show a) => Show (Expr m a) where
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
      # VariantF.on (SProxy :: SProxy "None")
        (const "mkNone")
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
      # VariantF.on (SProxy :: SProxy "Some")
        (\(Identity v) -> "(mkSome " <> v <> ")")
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
      # VariantF.on (SProxy :: SProxy "OptionalLit")
        (\(Product (Tuple (Identity ty) lit)) -> "(mkOptionalLit " <> ty <> mb lit <> ")")
      # VariantF.on (SProxy :: SProxy "Pi")
        (\(BindingBody n t b) -> "(mkPi " <> n <> t <> b <> ")")
      # VariantF.on (SProxy :: SProxy "Project")
        (\(Tuple (App projs) e) -> "(mkProject " <> e <> rec (show <$> projs) <> ")")
      # VariantF.on (SProxy :: SProxy "Record")
        (\a -> "(mkRecord " <> rec a <> ")")
      # VariantF.on (SProxy :: SProxy "RecordLit")
        (\a -> "(mkRecordLit " <> rec a <> ")")
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
        (\a -> "(mkUnion " <> rec a <> ")")
      # VariantF.on (SProxy :: SProxy "UnionLit")
        (\(Product (Tuple (Tuple ty val) a)) -> "(mkUnionLit " <> ty <> val <> rec a <> ")")
      )

instance eqExpr :: (Eq1 m, Eq a) => Eq (Expr m a) where
  eq e1 e2 = project e1 `eq1` project e2
instance eq1Expr :: (Eq1 m) => Eq1 (Expr m) where
  eq1 = eq
instance ordExpr :: (Ord1 m, Ord a) => Ord (Expr m a) where
  compare e1 e2 = project e1 `compare1` project e2
instance ord1Expr :: (Ord1 m) => Ord1 (Expr m) where
  compare1 = compare

vfCase ::
  forall sym fnc v' v v1' v1 a r.
    IsSymbol sym =>
    Row.Cons sym (FProxy fnc) v' v =>
    Row.Cons sym (FProxy fnc) v1' v1 =>
  r ->
  (fnc a -> fnc a -> r) ->
  SProxy sym ->
  (VariantF v' a -> VariantF v1 a -> r) ->
  VariantF v a -> VariantF v1 a -> r
vfCase df f k = VariantF.on k (\a -> VariantF.default df # VariantF.on k (f a))

vfEqCase ::
  forall sym fnc v' v v1' v1 a.
    IsSymbol sym =>
    Eq (fnc a) =>
    Row.Cons sym (FProxy fnc) v' v =>
    Row.Cons sym (FProxy fnc) v1' v1 =>
  SProxy sym ->
  (VariantF v' a -> VariantF v1 a -> Boolean) ->
  VariantF v a -> VariantF v1 a -> Boolean
vfEqCase = vfCase false eq

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
vfEq1Case = vfCase false eq1

vfOrdCase ::
  forall sym fnc v' v v1' v1 a.
    IsSymbol sym =>
    Ord (fnc a) =>
    Row.Cons sym (FProxy fnc) v' v =>
    Row.Cons sym (FProxy fnc) v1' v1 =>
  SProxy sym ->
  (VariantF v' a -> VariantF v1 a -> Ordering) ->
  VariantF v a -> VariantF v1 a -> Ordering
vfOrdCase = vfCase LT compare

vfOrd1Case ::
  forall sym fnc v' v v1' v1 a.
    IsSymbol sym =>
    Ord1 fnc =>
    Ord a =>
    Row.Cons sym (FProxy fnc) v' v =>
    Row.Cons sym (FProxy fnc) v1' v1 =>
  SProxy sym ->
  (VariantF v' a -> VariantF v1 a -> Ordering) ->
  VariantF v a -> VariantF v1 a -> Ordering
vfOrd1Case = vfCase LT compare1

-- A newtype for ... reasons
newtype ExprRowVF m a b = ERVF (ExprLayerF m a b)
derive instance newtypeERVF :: Newtype (ExprRowVF m a b) _
derive newtype instance functorERVF :: Functor (ExprRowVF m a)
derive newtype instance foldableERVF :: Foldable m => Foldable (ExprRowVF m a)
derive newtype instance traversableERVF :: Traversable m => Traversable (ExprRowVF m a)
derive newtype instance mergeERVF :: (Eq a, Eq1 m, Merge m) => Merge (ExprRowVF m a)
instance bifunctorERVF :: Bifunctor (ExprRowVF m) where
  bimap f g (ERVF v) = ERVF $ map g $ (#) v $
    VariantF.expand # VariantF.on (SProxy :: SProxy "Embed")
      (lmap f >>> VariantF.inj (SProxy :: SProxy "Embed"))
newtype ExprRowVF' m m' a b = ERVF' (ExprLayerF' m m' a b)
derive instance newtypeERVF' :: Newtype (ExprRowVF' m m' a b) _
derive newtype instance functorERVF' :: Functor (ExprRowVF' m m' a)
derive newtype instance foldableERVF' :: (Foldable m, Foldable m') => Foldable (ExprRowVF' m m' a)
derive newtype instance traversableERVF' :: (Traversable m, Traversable m') => Traversable (ExprRowVF' m m' a)
derive newtype instance mergeERVF' :: (Eq1 m, Merge m, Merge m') => Merge (ExprRowVF' m m' a)
newtype ExprRowVFI = ERVFI ExprLayerFI
derive instance newtypeERVFI :: Newtype ExprRowVFI _
derive newtype instance eqERVFI :: Eq ExprRowVFI
derive newtype instance ordERVFI :: Ord ExprRowVFI

instance functorWithIndexERVF :: FunctorWithIndex String m => FunctorWithIndex ExprRowVFI (ExprRowVF m a) where
  mapWithIndex f (ERVF v) = ERVF (mapWithIndexV (f <<< ERVFI) v)
instance foldableWithIndexERVF :: (FunctorWithIndex String m, FoldableWithIndex String m) => FoldableWithIndex ExprRowVFI (ExprRowVF m a) where
  foldrWithIndex f z = foldr (\(Tuple i a) z' -> f i a z') z <<< mapWithIndex Tuple
  foldlWithIndex f z = foldl (\z' (Tuple i a) -> f i z' a) z <<< mapWithIndex Tuple
  foldMapWithIndex f = fold <<< mapWithIndex f
instance traversableWithIndexERVF :: TraversableWithIndex String m => TraversableWithIndex ExprRowVFI (ExprRowVF m a) where
  traverseWithIndex f = sequence <<< mapWithIndex f

instance eqExprRowVF :: (Eq1 m, Eq a, Eq b) => Eq (ExprRowVF m a b) where
  eq = eq1
instance eq1ExprRowVF :: (Eq1 m, Eq a) => Eq1 (ExprRowVF m a) where
  eq1 (ERVF e1) (ERVF e2) =
    ( VariantF.case_
    # vfEqCase (SProxy :: SProxy "Annot")
    # vfEqCase (SProxy :: SProxy "App")
    # vfEqCase (SProxy :: SProxy "Bool")
    # vfEqCase (SProxy :: SProxy "BoolAnd")
    # vfEqCase (SProxy :: SProxy "BoolEQ")
    # vfEqCase (SProxy :: SProxy "BoolIf")
    # vfEqCase (SProxy :: SProxy "BoolLit")
    # vfEqCase (SProxy :: SProxy "BoolNE")
    # vfEqCase (SProxy :: SProxy "BoolOr")
    # vfEqCase (SProxy :: SProxy "Combine")
    # vfEqCase (SProxy :: SProxy "CombineTypes")
    # vfEqCase (SProxy :: SProxy "Const")
    # vfEqCase (SProxy :: SProxy "Constructors")
    # vfEqCase (SProxy :: SProxy "Double")
    # vfEqCase (SProxy :: SProxy "DoubleLit")
    # vfEqCase (SProxy :: SProxy "DoubleShow")
    # vfEqCase (SProxy :: SProxy "Embed")
    # vfEqCase (SProxy :: SProxy "Field")
    # vfEqCase (SProxy :: SProxy "ImportAlt")
    # vfEqCase (SProxy :: SProxy "Integer")
    # vfEqCase (SProxy :: SProxy "IntegerLit")
    # vfEqCase (SProxy :: SProxy "IntegerShow")
    # vfEqCase (SProxy :: SProxy "IntegerToDouble")
    # vfEqCase (SProxy :: SProxy "Lam")
    # vfEqCase (SProxy :: SProxy "Let")
    # vfEqCase (SProxy :: SProxy "List")
    # vfEqCase (SProxy :: SProxy "ListAppend")
    # vfEqCase (SProxy :: SProxy "ListBuild")
    # vfEqCase (SProxy :: SProxy "ListFold")
    # vfEqCase (SProxy :: SProxy "ListHead")
    # vfEqCase (SProxy :: SProxy "ListIndexed")
    # vfEqCase (SProxy :: SProxy "ListLast")
    # vfEqCase (SProxy :: SProxy "ListLength")
    # vfEqCase (SProxy :: SProxy "ListLit")
    # vfEqCase (SProxy :: SProxy "ListReverse")
    # vfEqCase (SProxy :: SProxy "Merge")
    # vfEqCase (SProxy :: SProxy "Natural")
    # vfEqCase (SProxy :: SProxy "NaturalBuild")
    # vfEqCase (SProxy :: SProxy "NaturalEven")
    # vfEqCase (SProxy :: SProxy "NaturalFold")
    # vfEqCase (SProxy :: SProxy "NaturalIsZero")
    # vfEqCase (SProxy :: SProxy "NaturalLit")
    # vfEqCase (SProxy :: SProxy "NaturalOdd")
    # vfEqCase (SProxy :: SProxy "NaturalPlus")
    # vfEqCase (SProxy :: SProxy "NaturalShow")
    # vfEqCase (SProxy :: SProxy "NaturalTimes")
    # vfEqCase (SProxy :: SProxy "NaturalToInteger")
    # vfEqCase (SProxy :: SProxy "None")
    # vfEqCase (SProxy :: SProxy "Optional")
    # vfEqCase (SProxy :: SProxy "OptionalBuild")
    # vfEqCase (SProxy :: SProxy "OptionalFold")
    # vfEqCase (SProxy :: SProxy "OptionalLit")
    # vfEqCase (SProxy :: SProxy "Pi")
    # vfEqCase (SProxy :: SProxy "Prefer")
    # vfEqCase (SProxy :: SProxy "Project")
    # vfEq1Case (SProxy :: SProxy "Record")
    # vfEq1Case (SProxy :: SProxy "RecordLit")
    # vfEq1Case (SProxy :: SProxy "Some")
    # vfEqCase (SProxy :: SProxy "Text")
    # vfEqCase (SProxy :: SProxy "TextAppend")
    # vfEqCase (SProxy :: SProxy "TextLit")
    # vfEq1Case (SProxy :: SProxy "Union")
    # vfEq1Case (SProxy :: SProxy "UnionLit")
    # vfEqCase (SProxy :: SProxy "Var")
    ) e1 e2

instance ordExprRowVF :: (Ord1 m, Ord a, Ord b) => Ord (ExprRowVF m a b) where
  compare = compare1
instance ord1ExprRowVF :: (Ord1 m, Ord a) => Ord1 (ExprRowVF m a) where
  compare1 (ERVF e1) (ERVF e2) =
    ( VariantF.case_
    # vfOrdCase (SProxy :: SProxy "Annot")
    # vfOrdCase (SProxy :: SProxy "App")
    # vfOrdCase (SProxy :: SProxy "Bool")
    # vfOrdCase (SProxy :: SProxy "BoolAnd")
    # vfOrdCase (SProxy :: SProxy "BoolEQ")
    # vfOrdCase (SProxy :: SProxy "BoolIf")
    # vfOrdCase (SProxy :: SProxy "BoolLit")
    # vfOrdCase (SProxy :: SProxy "BoolNE")
    # vfOrdCase (SProxy :: SProxy "BoolOr")
    # vfOrdCase (SProxy :: SProxy "Combine")
    # vfOrdCase (SProxy :: SProxy "CombineTypes")
    # vfOrdCase (SProxy :: SProxy "Const")
    # vfOrdCase (SProxy :: SProxy "Constructors")
    # vfOrdCase (SProxy :: SProxy "Double")
    # vfOrdCase (SProxy :: SProxy "DoubleLit")
    # vfOrdCase (SProxy :: SProxy "DoubleShow")
    # vfOrdCase (SProxy :: SProxy "Embed")
    # vfOrdCase (SProxy :: SProxy "Field")
    # vfOrdCase (SProxy :: SProxy "ImportAlt")
    # vfOrdCase (SProxy :: SProxy "Integer")
    # vfOrdCase (SProxy :: SProxy "IntegerLit")
    # vfOrdCase (SProxy :: SProxy "IntegerShow")
    # vfOrdCase (SProxy :: SProxy "IntegerToDouble")
    # vfOrdCase (SProxy :: SProxy "Lam")
    # vfOrdCase (SProxy :: SProxy "Let")
    # vfOrdCase (SProxy :: SProxy "List")
    # vfOrdCase (SProxy :: SProxy "ListAppend")
    # vfOrdCase (SProxy :: SProxy "ListBuild")
    # vfOrdCase (SProxy :: SProxy "ListFold")
    # vfOrdCase (SProxy :: SProxy "ListHead")
    # vfOrdCase (SProxy :: SProxy "ListIndexed")
    # vfOrdCase (SProxy :: SProxy "ListLast")
    # vfOrdCase (SProxy :: SProxy "ListLength")
    # vfOrdCase (SProxy :: SProxy "ListLit")
    # vfOrdCase (SProxy :: SProxy "ListReverse")
    # vfOrdCase (SProxy :: SProxy "Merge")
    # vfOrdCase (SProxy :: SProxy "Natural")
    # vfOrdCase (SProxy :: SProxy "NaturalBuild")
    # vfOrdCase (SProxy :: SProxy "NaturalEven")
    # vfOrdCase (SProxy :: SProxy "NaturalFold")
    # vfOrdCase (SProxy :: SProxy "NaturalIsZero")
    # vfOrdCase (SProxy :: SProxy "NaturalLit")
    # vfOrdCase (SProxy :: SProxy "NaturalOdd")
    # vfOrdCase (SProxy :: SProxy "NaturalPlus")
    # vfOrdCase (SProxy :: SProxy "NaturalShow")
    # vfOrdCase (SProxy :: SProxy "NaturalTimes")
    # vfOrdCase (SProxy :: SProxy "NaturalToInteger")
    # vfOrdCase (SProxy :: SProxy "None")
    # vfOrdCase (SProxy :: SProxy "Optional")
    # vfOrdCase (SProxy :: SProxy "OptionalBuild")
    # vfOrdCase (SProxy :: SProxy "OptionalFold")
    # vfOrdCase (SProxy :: SProxy "OptionalLit")
    # vfOrdCase (SProxy :: SProxy "Pi")
    # vfOrdCase (SProxy :: SProxy "Prefer")
    # vfOrdCase (SProxy :: SProxy "Project")
    # vfOrd1Case (SProxy :: SProxy "Record")
    # vfOrd1Case (SProxy :: SProxy "RecordLit")
    # vfOrd1Case (SProxy :: SProxy "Some")
    # vfOrdCase (SProxy :: SProxy "Text")
    # vfOrdCase (SProxy :: SProxy "TextAppend")
    # vfOrdCase (SProxy :: SProxy "TextLit")
    # vfOrd1Case (SProxy :: SProxy "Union")
    # vfOrd1Case (SProxy :: SProxy "UnionLit")
    # vfOrdCase (SProxy :: SProxy "Var")
    ) e1 e2

instance eqExprRowVF' :: (Eq1 m, Eq1 m', Eq a, Eq b) => Eq (ExprRowVF' m m' a b) where
  eq = eq1
instance eq1ExprRowVF' :: (Eq1 m, Eq1 m', Eq a) => Eq1 (ExprRowVF' m m' a) where
  eq1 (ERVF' e1) (ERVF' e2) =
    ( VariantF.case_
    # vfEqCase (SProxy :: SProxy "Annot")
    # vfEqCase (SProxy :: SProxy "App")
    # vfEqCase (SProxy :: SProxy "Bool")
    # vfEqCase (SProxy :: SProxy "BoolAnd")
    # vfEqCase (SProxy :: SProxy "BoolEQ")
    # vfEqCase (SProxy :: SProxy "BoolIf")
    # vfEqCase (SProxy :: SProxy "BoolLit")
    # vfEqCase (SProxy :: SProxy "BoolNE")
    # vfEqCase (SProxy :: SProxy "BoolOr")
    # vfEqCase (SProxy :: SProxy "Combine")
    # vfEqCase (SProxy :: SProxy "CombineTypes")
    # vfEqCase (SProxy :: SProxy "Const")
    # vfEqCase (SProxy :: SProxy "Constructors")
    # vfEqCase (SProxy :: SProxy "Double")
    # vfEqCase (SProxy :: SProxy "DoubleLit")
    # vfEqCase (SProxy :: SProxy "DoubleShow")
    # vfEqCase (SProxy :: SProxy "Embed")
    # vfEqCase (SProxy :: SProxy "Field")
    # vfEqCase (SProxy :: SProxy "ImportAlt")
    # vfEqCase (SProxy :: SProxy "Integer")
    # vfEqCase (SProxy :: SProxy "IntegerLit")
    # vfEqCase (SProxy :: SProxy "IntegerShow")
    # vfEqCase (SProxy :: SProxy "IntegerToDouble")
    # vfEqCase (SProxy :: SProxy "Lam")
    # vfEqCase (SProxy :: SProxy "Let")
    # vfEqCase (SProxy :: SProxy "List")
    # vfEqCase (SProxy :: SProxy "ListAppend")
    # vfEqCase (SProxy :: SProxy "ListBuild")
    # vfEqCase (SProxy :: SProxy "ListFold")
    # vfEqCase (SProxy :: SProxy "ListHead")
    # vfEqCase (SProxy :: SProxy "ListIndexed")
    # vfEqCase (SProxy :: SProxy "ListLast")
    # vfEqCase (SProxy :: SProxy "ListLength")
    # vfEqCase (SProxy :: SProxy "ListLit")
    # vfEqCase (SProxy :: SProxy "ListReverse")
    # vfEqCase (SProxy :: SProxy "Merge")
    # vfEqCase (SProxy :: SProxy "Natural")
    # vfEqCase (SProxy :: SProxy "NaturalBuild")
    # vfEqCase (SProxy :: SProxy "NaturalEven")
    # vfEqCase (SProxy :: SProxy "NaturalFold")
    # vfEqCase (SProxy :: SProxy "NaturalIsZero")
    # vfEqCase (SProxy :: SProxy "NaturalLit")
    # vfEqCase (SProxy :: SProxy "NaturalOdd")
    # vfEqCase (SProxy :: SProxy "NaturalPlus")
    # vfEqCase (SProxy :: SProxy "NaturalShow")
    # vfEqCase (SProxy :: SProxy "NaturalTimes")
    # vfEqCase (SProxy :: SProxy "NaturalToInteger")
    # vfEqCase (SProxy :: SProxy "None")
    # vfEqCase (SProxy :: SProxy "Optional")
    # vfEqCase (SProxy :: SProxy "OptionalBuild")
    # vfEqCase (SProxy :: SProxy "OptionalFold")
    # vfEqCase (SProxy :: SProxy "OptionalLit")
    # vfEqCase (SProxy :: SProxy "Pi")
    # vfEqCase (SProxy :: SProxy "Prefer")
    # vfEqCase (SProxy :: SProxy "Project")
    # vfEq1Case (SProxy :: SProxy "Record")
    # vfEq1Case (SProxy :: SProxy "RecordLit")
    # vfEq1Case (SProxy :: SProxy "Some")
    # vfEqCase (SProxy :: SProxy "Text")
    # vfEqCase (SProxy :: SProxy "TextAppend")
    # vfEqCase (SProxy :: SProxy "TextLit")
    # vfEq1Case (SProxy :: SProxy "Union")
    # vfEq1Case (SProxy :: SProxy "UnionLit")
    # vfEqCase (SProxy :: SProxy "Var")
    ) e1 e2

instance ordExprRowVF' :: (Ord1 m, Ord1 m', Ord a, Ord b) => Ord (ExprRowVF' m m' a b) where
  compare = compare1
instance ord1ExprRowVF' :: (Ord1 m, Ord1 m', Ord a) => Ord1 (ExprRowVF' m m' a) where
  compare1 (ERVF' e1) (ERVF' e2) =
    ( VariantF.case_
    # vfOrdCase (SProxy :: SProxy "Annot")
    # vfOrdCase (SProxy :: SProxy "App")
    # vfOrdCase (SProxy :: SProxy "Bool")
    # vfOrdCase (SProxy :: SProxy "BoolAnd")
    # vfOrdCase (SProxy :: SProxy "BoolEQ")
    # vfOrdCase (SProxy :: SProxy "BoolIf")
    # vfOrdCase (SProxy :: SProxy "BoolLit")
    # vfOrdCase (SProxy :: SProxy "BoolNE")
    # vfOrdCase (SProxy :: SProxy "BoolOr")
    # vfOrdCase (SProxy :: SProxy "Combine")
    # vfOrdCase (SProxy :: SProxy "CombineTypes")
    # vfOrdCase (SProxy :: SProxy "Const")
    # vfOrdCase (SProxy :: SProxy "Constructors")
    # vfOrdCase (SProxy :: SProxy "Double")
    # vfOrdCase (SProxy :: SProxy "DoubleLit")
    # vfOrdCase (SProxy :: SProxy "DoubleShow")
    # vfOrdCase (SProxy :: SProxy "Embed")
    # vfOrdCase (SProxy :: SProxy "Field")
    # vfOrdCase (SProxy :: SProxy "ImportAlt")
    # vfOrdCase (SProxy :: SProxy "Integer")
    # vfOrdCase (SProxy :: SProxy "IntegerLit")
    # vfOrdCase (SProxy :: SProxy "IntegerShow")
    # vfOrdCase (SProxy :: SProxy "IntegerToDouble")
    # vfOrdCase (SProxy :: SProxy "Lam")
    # vfOrdCase (SProxy :: SProxy "Let")
    # vfOrdCase (SProxy :: SProxy "List")
    # vfOrdCase (SProxy :: SProxy "ListAppend")
    # vfOrdCase (SProxy :: SProxy "ListBuild")
    # vfOrdCase (SProxy :: SProxy "ListFold")
    # vfOrdCase (SProxy :: SProxy "ListHead")
    # vfOrdCase (SProxy :: SProxy "ListIndexed")
    # vfOrdCase (SProxy :: SProxy "ListLast")
    # vfOrdCase (SProxy :: SProxy "ListLength")
    # vfOrdCase (SProxy :: SProxy "ListLit")
    # vfOrdCase (SProxy :: SProxy "ListReverse")
    # vfOrdCase (SProxy :: SProxy "Merge")
    # vfOrdCase (SProxy :: SProxy "Natural")
    # vfOrdCase (SProxy :: SProxy "NaturalBuild")
    # vfOrdCase (SProxy :: SProxy "NaturalEven")
    # vfOrdCase (SProxy :: SProxy "NaturalFold")
    # vfOrdCase (SProxy :: SProxy "NaturalIsZero")
    # vfOrdCase (SProxy :: SProxy "NaturalLit")
    # vfOrdCase (SProxy :: SProxy "NaturalOdd")
    # vfOrdCase (SProxy :: SProxy "NaturalPlus")
    # vfOrdCase (SProxy :: SProxy "NaturalShow")
    # vfOrdCase (SProxy :: SProxy "NaturalTimes")
    # vfOrdCase (SProxy :: SProxy "NaturalToInteger")
    # vfOrdCase (SProxy :: SProxy "None")
    # vfOrdCase (SProxy :: SProxy "Optional")
    # vfOrdCase (SProxy :: SProxy "OptionalBuild")
    # vfOrdCase (SProxy :: SProxy "OptionalFold")
    # vfOrdCase (SProxy :: SProxy "OptionalLit")
    # vfOrdCase (SProxy :: SProxy "Pi")
    # vfOrdCase (SProxy :: SProxy "Prefer")
    # vfOrdCase (SProxy :: SProxy "Project")
    # vfOrd1Case (SProxy :: SProxy "Record")
    # vfOrd1Case (SProxy :: SProxy "RecordLit")
    # vfOrd1Case (SProxy :: SProxy "Some")
    # vfOrdCase (SProxy :: SProxy "Text")
    # vfOrdCase (SProxy :: SProxy "TextAppend")
    # vfOrdCase (SProxy :: SProxy "TextLit")
    # vfOrd1Case (SProxy :: SProxy "Union")
    # vfOrd1Case (SProxy :: SProxy "UnionLit")
    # vfOrdCase (SProxy :: SProxy "Var")
    ) e1 e2

instance containerIERVF :: ContainerI String m' => ContainerI ExprRowVFI (ExprRowVF' m m' a) where
  ixF (ERVF' e) = ERVFI (ixFV e)

instance containerERVF :: (Ord a, Functor m', Eq1 m, Merge m, Traversable m, Container String m m') => Container ExprRowVFI (ExprRowVF m a) (ExprRowVF' m m' a) where
  downZF (ERVF e) = ERVF (downZFV e <#> _contextZF ERVF')
  upZF (a :<-: e) = ERVF (upZFV (a :<-: pure (unwrap (extract e))))

derive newtype instance functorExpr :: Functor (Expr m)
derive newtype instance applyExpr :: Apply (Expr m)
derive newtype instance applicativeExpr :: Applicative (Expr m)
derive newtype instance bindExpr :: Bind (Expr m)
derive newtype instance monadExpr :: Monad (Expr m)
derive newtype instance foldableExpr :: Foldable m => Foldable (Expr m)
-- Traversable will allow running computations on the embedded data,
-- e.g. using an error monad to get rid of holes, or using Aff to fill in
-- imports (especially via URL).
derive newtype instance traversableExpr :: Traversable m => Traversable (Expr m)

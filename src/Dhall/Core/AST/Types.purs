module Dhall.Core.AST.Types ( module Dhall.Core.AST.Types, module Exports ) where

import Prelude

import Control.Comonad (extract)
import Control.Monad.Free (Free)
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Bifunctor (class Bifunctor, lmap)
import Data.Const as ConstF
import Data.Either (Either(..), either)
import Data.Eq (class Eq1, eq1)
import Data.Foldable (class Foldable, fold, foldl, foldr)
import Data.FoldableWithIndex (class FoldableWithIndex, foldMapWithIndex)
import Data.Functor.App (App(..))
import Data.Functor.Compose (Compose)
import Data.Functor.Product (Product(..))
import Data.Functor.Variant (VariantF)
import Data.Functor.Variant as VariantF
import Data.FunctorWithIndex (class FunctorWithIndex, mapWithIndex)
import Data.Identity (Identity(..))
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, un, unwrap, wrap)
import Data.Ord (class Ord1, compare1)
import Data.String (joinWith)
import Data.Symbol (class IsSymbol)
import Data.Traversable (class Traversable, sequence)
import Data.TraversableWithIndex (class TraversableWithIndex)
import Data.Tuple (Tuple(..))
import Data.Variant (Variant)
import Dhall.Core.AST.Types.Basics (_S, S_, BindingBody(..), BindingBody', BindingBodyI, CONST, LetF(..), LetF', LetFI, MergeF(..), MergeF', MergeFI, Pair(..), Pair', PairI, TextLitF(..), TextLitF', TextLitFI, Triplet(..), Triplet', TripletI, UNIT, VOID)
import Dhall.Core.Zippers (class Container, class ContainerI, Array', ArrayI, Compose', Either', EitherI, Identity', IdentityI, Maybe', MaybeI, Product', ProductI, Tuple', TupleI, ComposeI, _contextZF, downZFV, ixFV, mapWithIndexV, upZFV, (:<-:))
import Dhall.Core.Zippers.Merge (class Merge)
import Dhall.Core.Zippers.Recursive (ZRec, Indices)
import Dhall.Lib.Numbers (Double, Integer, Natural)
import Dhall.Lib.Numbers (Double(..), Integer(..), Natural(..), intToInteger, integerFromString, integerToInt, integerToInt', integerToNumber, naturalFromInt, naturalFromInteger, naturalToInteger) as Exports
import Matryoshka (class Corecursive, class Recursive, cata, embed, project)
import Prim.Row as Row
import Type.Proxy (Proxy)

-- This file defines the Expr type by its cases, and gives instances, etc.

-- copied from dhall-haskell
data Const = Type | Kind | Sort
derive instance eqConst :: Eq Const
derive instance ordConst :: Ord Const
instance showConst :: Show Const where
  show Type = "Type"
  show Kind = "Kind"
  show Sort = "Sort"

-- copied from dhall-haskell
data Var = V String Int
derive instance eqVar :: Eq Var
derive instance ordVar :: Ord Var
instance showVar :: Show Var where
  show (V name idx) = name <> "@" <> show idx

-- Constant (non-recursive) literal types; the base of the AST, essentially
type Literals (m :: Type -> Type) vs =
  ( "BoolLit" :: CONST Boolean
  , "NaturalLit" :: CONST Natural
  , "IntegerLit" :: CONST Integer
  , "DoubleLit" :: CONST Double
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
  ( "TextLit" :: TextLitF
  , "ListLit" :: Product Maybe Array
  , "Some" :: Identity
  , "None" :: CONST Unit
  , "RecordLit" :: m
  | v
  )

type Literals2' (m :: Type -> Type) (m' :: Type -> Type) v =
  ( "TextLit" :: TextLitF'
  , "ListLit" :: Product' Maybe Maybe' Array Array'
  , "Some" :: Identity'
  , "None" :: VOID
  , "RecordLit" :: m'
  | v
  )

type Literals2I v =
  ( "TextLit" :: TextLitFI
  , "ListLit" :: ProductI MaybeI ArrayI
  , "Some" :: IdentityI
  , "None" :: Void
  , "RecordLit" :: String
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
  ( "Record" :: m
  , "Union" :: Compose m Maybe
  | v
  )

type BuiltinTypes2' (m :: Type -> Type) (m' :: Type -> Type) v =
  ( "Record" :: m'
  , "Union" :: Compose' m' Maybe Maybe'
  | v
  )

type BuiltinTypes2I v =
  ( "Record" :: String
  , "Union" :: ComposeI String MaybeI
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
  , "NaturalSubtract" :: UNIT
  , "IntegerShow" :: UNIT
  , "IntegerToDouble" :: UNIT
  , "IntegerNegate" :: UNIT
  , "IntegerClamp" :: UNIT
  , "DoubleShow" :: UNIT
  , "ListBuild" :: UNIT
  , "ListFold" :: UNIT
  , "ListLength" :: UNIT
  , "ListHead" :: UNIT
  , "ListLast" :: UNIT
  , "ListIndexed" :: UNIT
  , "ListReverse" :: UNIT
  , "TextShow" :: UNIT
  , "TextReplace" :: UNIT
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
  , "NaturalSubtract" :: VOID
  , "IntegerShow" :: VOID
  , "IntegerToDouble" :: VOID
  , "IntegerNegate" :: VOID
  , "IntegerClamp" :: VOID
  , "DoubleShow" :: VOID
  , "ListBuild" :: VOID
  , "ListFold" :: VOID
  , "ListLength" :: VOID
  , "ListHead" :: VOID
  , "ListLast" :: VOID
  , "ListIndexed" :: VOID
  , "ListReverse" :: VOID
  , "TextShow" :: VOID
  , "TextReplace" :: VOID
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
  , "NaturalSubtract" :: Void
  , "IntegerShow" :: Void
  , "IntegerToDouble" :: Void
  , "IntegerNegate" :: Void
  , "IntegerClamp" :: Void
  , "DoubleShow" :: Void
  , "ListBuild" :: Void
  , "ListFold" :: Void
  , "ListLength" :: Void
  , "ListHead" :: Void
  , "ListLast" :: Void
  , "ListIndexed" :: Void
  , "ListReverse" :: Void
  , "TextShow" :: Void
  , "TextReplace" :: Void
  | vs
  )

-- And binary operations
type BuiltinBinOps (m :: Type -> Type) vs =
  ( "BoolAnd" :: Pair
  , "BoolOr" :: Pair
  , "BoolEQ" :: Pair
  , "BoolNE" :: Pair
  , "NaturalPlus" :: Pair
  , "NaturalTimes" :: Pair
  , "TextAppend" :: Pair
  , "ListAppend" :: Pair
  , "Combine" :: Pair
  , "CombineTypes" :: Pair
  , "Prefer" :: Pair
  , "Equivalent" :: Pair
  , "RecordCompletion" :: Pair
  | vs
  )

type BuiltinBinOps' (m :: Type -> Type) (m' :: Type -> Type) vs =
  ( "BoolAnd" :: Pair'
  , "BoolOr" :: Pair'
  , "BoolEQ" :: Pair'
  , "BoolNE" :: Pair'
  , "NaturalPlus" :: Pair'
  , "NaturalTimes" :: Pair'
  , "TextAppend" :: Pair'
  , "ListAppend" :: Pair'
  , "Combine" :: Pair'
  , "CombineTypes" :: Pair'
  , "Prefer" :: Pair'
  , "Equivalent" :: Pair'
  , "RecordCompletion" :: Pair'
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
  , "Equivalent" :: PairI
  , "RecordCompletion" :: PairI
  | vs
  )

-- All builtin operations with their own syntax
type BuiltinOps (m :: Type -> Type) v = BuiltinBinOps m
  ( "BoolIf" :: Triplet
  , "Field" :: Tuple String
  , "With" :: Product Identity (Tuple (NonEmptyArray String))
  , "Project" :: Product Identity (Either (App m Unit))
  , "Merge" :: MergeF
  , "ToMap" :: Product Identity Maybe
  , "Assert" :: Identity
  | v
  )

type BuiltinOps' (m :: Type -> Type) (m' :: Type -> Type) v = BuiltinBinOps' m m'
  ( "BoolIf" :: Triplet'
  , "Field" :: Tuple' String
  , "With" :: Product' Identity Identity' (Tuple (NonEmptyArray String)) (Tuple' (NonEmptyArray String))
  , "Project" :: Product' Identity Identity' (Either (App m Unit)) (Either' (App m Unit))
  , "Merge" :: MergeF'
  , "ToMap" :: Product' Identity Identity' Maybe Maybe'
  , "Assert" :: Identity'
  | v
  )

type BuiltinOpsI v = BuiltinBinOpsI
  ( "BoolIf" :: TripletI
  , "Field" :: TupleI String
  , "With" :: ProductI IdentityI (TupleI (NonEmptyArray String))
  , "Project" :: ProductI IdentityI EitherI
  , "Merge" :: MergeFI
  , "ToMap" :: ProductI IdentityI MaybeI
  , "Assert" :: IdentityI
  | v
  )

type Variable (m :: Type -> Type) v =
  ( "Lam" :: BindingBody
  , "Pi" :: BindingBody
  , "Let" :: LetF
  , "Var" :: CONST Var
  | v
  )

type Variable' (m :: Type -> Type) (m' :: Type -> Type) v =
  ( "Lam" :: BindingBody'
  , "Pi" :: BindingBody'
  , "Let" :: LetF'
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
  ( "App" :: Pair
  , "Annot" :: Pair
  | v
  )

type Syntax' (m :: Type -> Type) (m' :: Type -> Type) v =
  ( "App" :: Pair'
  , "Annot" :: Pair'
  | v
  )

type SyntaxI v =
  ( "App" :: PairI
  , "Annot" :: PairI
  | v
  )

type ImportSyntax (m :: Type -> Type) v =
  ( "ImportAlt" :: Pair
  , "UsingHeaders" :: Pair
  , "Hashed" :: Tuple String -- Todo: better type?
  | v
  )

type ImportSyntax' (m :: Type -> Type) (m' :: Type -> Type) v =
  ( "ImportAlt" :: Pair'
  , "UsingHeaders" :: Pair'
  , "Hashed" :: Tuple' String
  | v
  )

type ImportSyntaxI v =
  ( "ImportAlt" :: PairI
  , "UsingHeaders" :: PairI
  , "Hashed" :: TupleI String
  | v
  )

-- Non-recursive items
type SimpleThings m vs = Literals m (BuiltinTypes m (BuiltinFuncs m vs))
type SimpleThings' m m' vs = Literals' m m' (BuiltinTypes' m m' (BuiltinFuncs' m m' vs))
type SimpleThingsI vs = LiteralsI (BuiltinTypesI (BuiltinFuncsI vs))

-- Recursive items
type FunctorThings m v = Literals2 m (BuiltinTypes2 m (BuiltinOps m (Syntax m (Variable m (ImportSyntax m v)))))
type FunctorThings' m m' v = Literals2' m m' (BuiltinTypes2' m m' (BuiltinOps' m m' (Syntax' m m' (Variable' m m' (ImportSyntax' m m' v)))))
type FunctorThingsI v = Literals2I (BuiltinTypes2I (BuiltinOpsI (SyntaxI (VariableI (ImportSyntaxI v)))))

-- Both together
type AllTheThings m v = SimpleThings m (FunctorThings m v)
type AllTheThings' m m' v = SimpleThings' m m' (FunctorThings' m m' v)
type AllTheThingsI v = SimpleThingsI (FunctorThingsI v)

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
type ExprLayerRow' m m' (a :: Type) =
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
    (wrap >>> VariantF.inj (_S::S_ "Embed"))
    VariantF.expand >>> ERVF

instance corecursiveExpr :: Corecursive (Expr m a) (ExprRowVF m a) where
  embed = wrap <<< embed <<< map (un Expr) <<< wrap <<<
    VariantF.on (_S::S_ "Embed") (Left <<< unwrap) Right <<< un ERVF

-- Project and unwrap the ExprRowVF newtype, to allow instant handling of the
-- cases via VariantF's api.
projectW :: forall m a. Expr m a -> ExprLayer m a
projectW = project >>> unwrap

embedW :: forall m a. ExprLayer m a -> Expr m a
embedW = embed <<< wrap

-- Really ugly showing for Expr
instance showExpr :: (TraversableWithIndex String m, Show a) => Show (Expr m a) where
  show (Expr e0) = cata show1 e0 where
    lits e = "(mkIOSM[" <> joinWith ", " e <> "])"
    rec e = lits $ foldMapWithIndex (\k v -> ["(Tuple " <> show k <> v <> ")"]) e
    mb =
      case _ of
        Nothing -> "(Nothing)"
        Just s -> "(Just " <> s <> ")"
    binop tag (Pair l r) = "(mk" <> tag <> " " <> l <> r <> ")"
    simple s = const ("(" <> s <> ")")
    show1 = unwrap >>> either (\e -> "(mkEmbed (" <> show e <> "))")
      ( VariantF.case_
      # VariantF.on (_S::S_ "None")
        (simple "mkNone")
      # VariantF.on (_S::S_ "Annot")
        (\(Pair l r) -> "(mkAnnot " <> l <> r <> ")")
      # VariantF.on (_S::S_ "App")
        (\(Pair l r) -> "(mkApp " <> l <> r <> ")")
      # VariantF.on (_S::S_ "BoolAnd") (binop "BoolAnd")
      # VariantF.on (_S::S_ "BoolOr") (binop "BoolOr")
      # VariantF.on (_S::S_ "BoolEQ") (binop "BoolEQ")
      # VariantF.on (_S::S_ "BoolNE") (binop "BoolNE")
      # VariantF.on (_S::S_ "NaturalPlus") (binop "NaturalPlus")
      # VariantF.on (_S::S_ "NaturalTimes") (binop "NaturalTimes")
      # VariantF.on (_S::S_ "TextAppend") (binop "TextAppend")
      # VariantF.on (_S::S_ "ListAppend") (binop "ListAppend")
      # VariantF.on (_S::S_ "Combine") (binop "Combine")
      # VariantF.on (_S::S_ "CombineTypes") (binop "CombineTypes")
      # VariantF.on (_S::S_ "Prefer") (binop "Prefer")
      # VariantF.on (_S::S_ "ImportAlt") (binop "ImportAlt")
      # VariantF.on (_S::S_ "UsingHeaders") (binop "UsingHeaders")
      # VariantF.on (_S::S_ "Equivalent") (binop "Equivalent")
      # VariantF.on (_S::S_ "RecordCompletion") (binop "RecordCompletion")
      # VariantF.on (_S::S_ "Hashed")
        (\(Tuple hash e) -> "(mkHashed " <> show hash <> " " <> e <> ")")
      # VariantF.on (_S::S_ "BoolIf")
        (\(Triplet c t f) -> "(mkBoolIf " <> c <> t <> f <> ")")
      # VariantF.on (_S::S_ "Some")
        (\(Identity v) -> "(mkSome " <> v <> ")")
      # VariantF.on (_S::S_ "Assert")
        (\(Identity v) -> "(mkAssert " <> v <> ")")
      # VariantF.on (_S::S_ "Field")
        (\(Tuple field e) -> "(mkField " <> e <> show field <> ")")
      # VariantF.on (_S::S_ "Lam")
        (\(BindingBody n t b) -> "(mkLam " <> show n <> t <> b <> ")")
      # VariantF.on (_S::S_ "Let")
        (\(LetF n t e b) -> "(mkLet " <> n <> mb t <> e <> b <> ")")
      # VariantF.on (_S::S_ "ListLit")
        (\(Product (Tuple ty lit)) -> "(mkListLit " <> mb ty <> lits lit <> ")")
      # VariantF.on (_S::S_ "With")
        (\(Product (Tuple (Identity e) (Tuple fs v))) -> "(mkWith " <> e <> show fs <> v <> ")")
      # VariantF.on (_S::S_ "Merge")
        (\(MergeF a b c) -> "(mkMerge " <> a <> b <> mb c <> ")")
      # VariantF.on (_S::S_ "ToMap")
        (\(Product (Tuple (Identity e) ty)) -> "(mkToMap " <> e <> mb ty <> ")")
      # VariantF.on (_S::S_ "Pi")
        (\(BindingBody n t b) -> "(mkPi " <> show n <> t <> b <> ")")
      # VariantF.on (_S::S_ "Project")
        (\(Product (Tuple (Identity e) projs)) -> case projs of
          Left (App fields) -> "(mkProject " <> e <> " (Left " <> rec (show <$> fields) <> "))"
          Right ef -> "(mkProject " <> e <> " (Right " <> ef <> "))")
      # VariantF.on (_S::S_ "Record")
        (\a -> "(mkRecord " <> rec a <> ")")
      # VariantF.on (_S::S_ "RecordLit")
        (\a -> "(mkRecordLit " <> rec a <> ")")
      # VariantF.on (_S::S_ "BoolLit")
        (unwrap >>> \b -> "(mkBoolLit " <> show b <> ")")
      # VariantF.on (_S::S_ "NaturalLit")
        (unwrap >>> \b -> "(mkNaturalLit " <> show b <> ")")
      # VariantF.on (_S::S_ "IntegerLit")
        (unwrap >>> \b -> "(mkIntegerLit " <> show b <> ")")
      # VariantF.on (_S::S_ "DoubleLit")
        (unwrap >>> \b -> "(mkDoubleLit " <> show b <> ")")
      # VariantF.on (_S::S_ "Bool") (simple "mkBool")
      # VariantF.on (_S::S_ "Natural") (simple "mkNatural")
      # VariantF.on (_S::S_ "Integer") (simple "mkInteger")
      # VariantF.on (_S::S_ "Double") (simple "mkDouble")
      # VariantF.on (_S::S_ "Text") (simple "mkText")
      # VariantF.on (_S::S_ "List") (simple "mkList")
      # VariantF.on (_S::S_ "Optional") (simple "mkOptional")
      # VariantF.on (_S::S_ "NaturalFold") (simple "mkNaturalFold")
      # VariantF.on (_S::S_ "NaturalBuild") (simple "mkNaturalBuild")
      # VariantF.on (_S::S_ "NaturalIsZero") (simple "mkNaturalIsZero")
      # VariantF.on (_S::S_ "NaturalEven") (simple "mkNaturalEven")
      # VariantF.on (_S::S_ "NaturalOdd") (simple "mkNaturalOdd")
      # VariantF.on (_S::S_ "NaturalToInteger") (simple "mkNaturalToInteger")
      # VariantF.on (_S::S_ "NaturalShow") (simple "mkNaturalShow")
      # VariantF.on (_S::S_ "NaturalSubtract") (simple "mkNaturalSubtract")
      # VariantF.on (_S::S_ "IntegerShow") (simple "mkIntegerShow")
      # VariantF.on (_S::S_ "IntegerToDouble") (simple "mkIntegerToDouble")
      # VariantF.on (_S::S_ "IntegerNegate") (simple "mkIntegerNegate")
      # VariantF.on (_S::S_ "IntegerClamp") (simple "mkIntegerClamp")
      # VariantF.on (_S::S_ "DoubleShow") (simple "mkDoubleShow")
      # VariantF.on (_S::S_ "ListBuild") (simple "mkListBuild")
      # VariantF.on (_S::S_ "ListFold") (simple "mkListFold")
      # VariantF.on (_S::S_ "ListLength") (simple "mkListLength")
      # VariantF.on (_S::S_ "ListHead") (simple "mkListHead")
      # VariantF.on (_S::S_ "ListLast") (simple "mkListLast")
      # VariantF.on (_S::S_ "ListIndexed") (simple "mkListIndexed")
      # VariantF.on (_S::S_ "ListReverse") (simple "mkListReverse")
      # VariantF.on (_S::S_ "TextShow") (simple "mkTextShow")
      # VariantF.on (_S::S_ "TextReplace") (simple "mkTextReplace")
      # VariantF.on (_S::S_ "Const")
        (case _ of
          ConstF.Const Type -> "(mkConst Type)"
          ConstF.Const Kind -> "(mkConst Kind)"
          ConstF.Const Sort -> "(mkConst Sort)"
        )
      # VariantF.on (_S::S_ "Var")
        (unwrap >>> \(V n x) -> "(mkVar (V " <> show n <> show x <> "))")
      # VariantF.on (_S::S_ "TextLit")
          (\e ->
            let
              v e' = case e' of
                TextLit s -> "(TextLit " <> show s <> ")"
                TextInterp s e'' m -> "(TextInterp " <> show s <> e'' <> v m <> ")"
            in "(mkTextLit " <> v e <> ")"
          )
      # VariantF.on (_S::S_ "Union")
        (\a -> "(mkUnion " <> rec (mb <$> unwrap a) <> ")")
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
    Row.Cons sym fnc v' v =>
    Row.Cons sym fnc v1' v1 =>
  r ->
  (fnc a -> fnc a -> r) ->
  Proxy sym ->
  (VariantF v' a -> VariantF v1 a -> r) ->
  VariantF v a -> VariantF v1 a -> r
vfCase df f k = VariantF.on k (\a -> VariantF.default df # VariantF.on k (f a))

vfEqCase ::
  forall sym fnc v' v v1' v1 a.
    IsSymbol sym =>
    Eq (fnc a) =>
    Row.Cons sym fnc v' v =>
    Row.Cons sym fnc v1' v1 =>
  Proxy sym ->
  (VariantF v' a -> VariantF v1 a -> Boolean) ->
  VariantF v a -> VariantF v1 a -> Boolean
vfEqCase = vfCase false eq

vfEq1Case ::
  forall sym fnc v' v v1' v1 a.
    IsSymbol sym =>
    Eq1 fnc =>
    Eq a =>
    Row.Cons sym fnc v' v =>
    Row.Cons sym fnc v1' v1 =>
  Proxy sym ->
  (VariantF v' a -> VariantF v1 a -> Boolean) ->
  VariantF v a -> VariantF v1 a -> Boolean
vfEq1Case = vfCase false eq1

vfOrdCase ::
  forall sym fnc v' v v1' v1 a.
    IsSymbol sym =>
    Ord (fnc a) =>
    Row.Cons sym fnc v' v =>
    Row.Cons sym fnc v1' v1 =>
  Proxy sym ->
  (VariantF v' a -> VariantF v1 a -> Ordering) ->
  VariantF v a -> VariantF v1 a -> Ordering
vfOrdCase = vfCase LT compare

vfOrd1Case ::
  forall sym fnc v' v v1' v1 a.
    IsSymbol sym =>
    Ord1 fnc =>
    Ord a =>
    Row.Cons sym fnc v' v =>
    Row.Cons sym fnc v1' v1 =>
  Proxy sym ->
  (VariantF v' a -> VariantF v1 a -> Ordering) ->
  VariantF v a -> VariantF v1 a -> Ordering
vfOrd1Case = vfCase LT compare1

-- A newtype for ... reasons
newtype ExprRowVF m a b = ERVF (ExprLayerF m a b)
derive instance newtypeERVF :: Newtype (ExprRowVF m a b) _
derive newtype instance functorERVF :: Functor (ExprRowVF m a)
derive newtype instance foldableERVF :: Foldable m => Foldable (ExprRowVF m a)
derive newtype instance traversableERVF :: Traversable m => Traversable (ExprRowVF m a)
derive newtype instance mergeERVF :: (Eq a, Eq1 m, Traversable m, Merge m) => Merge (ExprRowVF m a)
instance bifunctorERVF :: Bifunctor (ExprRowVF m) where
  bimap f g (ERVF v) = ERVF $ map g $ (#) v $
    VariantF.expand # VariantF.on (_S::S_ "Embed")
      (lmap f >>> VariantF.inj (_S::S_ "Embed"))
newtype ExprRowVF' m m' a b = ERVF' (ExprLayerF' m m' a b)
derive instance newtypeERVF' :: Newtype (ExprRowVF' m m' a b) _
derive newtype instance functorERVF' :: Functor (ExprRowVF' m m' a)
derive newtype instance foldableERVF' :: (Foldable m, Foldable m') => Foldable (ExprRowVF' m m' a)
derive newtype instance traversableERVF' :: (Traversable m, Traversable m') => Traversable (ExprRowVF' m m' a)
derive newtype instance mergeERVF' :: (Eq1 m, Traversable m, Traversable m', Merge m, Merge m') => Merge (ExprRowVF' m m' a)
newtype ExprRowVFI = ERVFI ExprLayerFI
derive instance newtypeERVFI :: Newtype ExprRowVFI _
derive newtype instance eqERVFI :: Eq ExprRowVFI
derive newtype instance ordERVFI :: Ord ExprRowVFI
derive newtype instance showERVFI :: Show ExprRowVFI

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
    # vfEqCase (_S::S_ "Annot")
    # vfEqCase (_S::S_ "App")
    # vfEqCase (_S::S_ "Assert")
    # vfEqCase (_S::S_ "Bool")
    # vfEqCase (_S::S_ "BoolAnd")
    # vfEqCase (_S::S_ "BoolEQ")
    # vfEqCase (_S::S_ "BoolIf")
    # vfEqCase (_S::S_ "BoolLit")
    # vfEqCase (_S::S_ "BoolNE")
    # vfEqCase (_S::S_ "BoolOr")
    # vfEqCase (_S::S_ "Combine")
    # vfEqCase (_S::S_ "CombineTypes")
    # vfEqCase (_S::S_ "Const")
    # vfEqCase (_S::S_ "Double")
    # vfEqCase (_S::S_ "DoubleLit")
    # vfEqCase (_S::S_ "DoubleShow")
    # vfEqCase (_S::S_ "Embed")
    # vfEqCase (_S::S_ "Equivalent")
    # vfEqCase (_S::S_ "Field")
    # vfEqCase (_S::S_ "Hashed")
    # vfEqCase (_S::S_ "ImportAlt")
    # vfEqCase (_S::S_ "Integer")
    # vfEqCase (_S::S_ "IntegerLit")
    # vfEqCase (_S::S_ "IntegerShow")
    # vfEqCase (_S::S_ "IntegerToDouble")
    # vfEqCase (_S::S_ "IntegerNegate")
    # vfEqCase (_S::S_ "IntegerClamp")
    # vfEqCase (_S::S_ "Lam")
    # vfEqCase (_S::S_ "Let")
    # vfEqCase (_S::S_ "List")
    # vfEqCase (_S::S_ "ListAppend")
    # vfEqCase (_S::S_ "ListBuild")
    # vfEqCase (_S::S_ "ListFold")
    # vfEqCase (_S::S_ "ListHead")
    # vfEqCase (_S::S_ "ListIndexed")
    # vfEqCase (_S::S_ "ListLast")
    # vfEqCase (_S::S_ "ListLength")
    # vfEqCase (_S::S_ "ListLit")
    # vfEqCase (_S::S_ "ListReverse")
    # vfEqCase (_S::S_ "Merge")
    # vfEqCase (_S::S_ "Natural")
    # vfEqCase (_S::S_ "NaturalBuild")
    # vfEqCase (_S::S_ "NaturalEven")
    # vfEqCase (_S::S_ "NaturalFold")
    # vfEqCase (_S::S_ "NaturalIsZero")
    # vfEqCase (_S::S_ "NaturalLit")
    # vfEqCase (_S::S_ "NaturalOdd")
    # vfEqCase (_S::S_ "NaturalPlus")
    # vfEqCase (_S::S_ "NaturalShow")
    # vfEqCase (_S::S_ "NaturalTimes")
    # vfEqCase (_S::S_ "NaturalToInteger")
    # vfEqCase (_S::S_ "NaturalSubtract")
    # vfEqCase (_S::S_ "None")
    # vfEqCase (_S::S_ "Optional")
    # vfEqCase (_S::S_ "Pi")
    # vfEqCase (_S::S_ "Prefer")
    # vfEqCase (_S::S_ "Project")
    # vfEq1Case (_S::S_ "Record")
    # vfEqCase (_S::S_ "RecordCompletion")
    # vfEq1Case (_S::S_ "RecordLit")
    # vfEq1Case (_S::S_ "Some")
    # vfEqCase (_S::S_ "Text")
    # vfEqCase (_S::S_ "TextAppend")
    # vfEqCase (_S::S_ "TextLit")
    # vfEqCase (_S::S_ "TextShow")
    # vfEqCase (_S::S_ "TextReplace")
    # vfEqCase (_S::S_ "ToMap")
    # vfEq1Case (_S::S_ "Union")
    # vfEqCase (_S::S_ "UsingHeaders")
    # vfEqCase (_S::S_ "Var")
    # vfEqCase (_S::S_ "With")
    ) e1 e2

instance ordExprRowVF :: (Ord1 m, Ord a, Ord b) => Ord (ExprRowVF m a b) where
  compare = compare1
instance ord1ExprRowVF :: (Ord1 m, Ord a) => Ord1 (ExprRowVF m a) where
  compare1 (ERVF e1) (ERVF e2) =
    ( VariantF.case_
    # vfOrdCase (_S::S_ "Annot")
    # vfOrdCase (_S::S_ "App")
    # vfOrdCase (_S::S_ "Assert")
    # vfOrdCase (_S::S_ "Bool")
    # vfOrdCase (_S::S_ "BoolAnd")
    # vfOrdCase (_S::S_ "BoolEQ")
    # vfOrdCase (_S::S_ "BoolIf")
    # vfOrdCase (_S::S_ "BoolLit")
    # vfOrdCase (_S::S_ "BoolNE")
    # vfOrdCase (_S::S_ "BoolOr")
    # vfOrdCase (_S::S_ "Combine")
    # vfOrdCase (_S::S_ "CombineTypes")
    # vfOrdCase (_S::S_ "Const")
    # vfOrdCase (_S::S_ "Double")
    # vfOrdCase (_S::S_ "DoubleLit")
    # vfOrdCase (_S::S_ "DoubleShow")
    # vfOrdCase (_S::S_ "Embed")
    # vfOrdCase (_S::S_ "Equivalent")
    # vfOrdCase (_S::S_ "Field")
    # vfOrdCase (_S::S_ "Hashed")
    # vfOrdCase (_S::S_ "ImportAlt")
    # vfOrdCase (_S::S_ "Integer")
    # vfOrdCase (_S::S_ "IntegerLit")
    # vfOrdCase (_S::S_ "IntegerShow")
    # vfOrdCase (_S::S_ "IntegerToDouble")
    # vfOrdCase (_S::S_ "IntegerNegate")
    # vfOrdCase (_S::S_ "IntegerClamp")
    # vfOrdCase (_S::S_ "Lam")
    # vfOrdCase (_S::S_ "Let")
    # vfOrdCase (_S::S_ "List")
    # vfOrdCase (_S::S_ "ListAppend")
    # vfOrdCase (_S::S_ "ListBuild")
    # vfOrdCase (_S::S_ "ListFold")
    # vfOrdCase (_S::S_ "ListHead")
    # vfOrdCase (_S::S_ "ListIndexed")
    # vfOrdCase (_S::S_ "ListLast")
    # vfOrdCase (_S::S_ "ListLength")
    # vfOrdCase (_S::S_ "ListLit")
    # vfOrdCase (_S::S_ "ListReverse")
    # vfOrdCase (_S::S_ "Merge")
    # vfOrdCase (_S::S_ "Natural")
    # vfOrdCase (_S::S_ "NaturalBuild")
    # vfOrdCase (_S::S_ "NaturalEven")
    # vfOrdCase (_S::S_ "NaturalFold")
    # vfOrdCase (_S::S_ "NaturalIsZero")
    # vfOrdCase (_S::S_ "NaturalLit")
    # vfOrdCase (_S::S_ "NaturalOdd")
    # vfOrdCase (_S::S_ "NaturalPlus")
    # vfOrdCase (_S::S_ "NaturalShow")
    # vfOrdCase (_S::S_ "NaturalTimes")
    # vfOrdCase (_S::S_ "NaturalToInteger")
    # vfOrdCase (_S::S_ "NaturalSubtract")
    # vfOrdCase (_S::S_ "None")
    # vfOrdCase (_S::S_ "Optional")
    # vfOrdCase (_S::S_ "Pi")
    # vfOrdCase (_S::S_ "Prefer")
    # vfOrdCase (_S::S_ "Project")
    # vfOrd1Case (_S::S_ "Record")
    # vfOrdCase (_S::S_ "RecordCompletion")
    # vfOrd1Case (_S::S_ "RecordLit")
    # vfOrd1Case (_S::S_ "Some")
    # vfOrdCase (_S::S_ "Text")
    # vfOrdCase (_S::S_ "TextAppend")
    # vfOrdCase (_S::S_ "TextLit")
    # vfOrdCase (_S::S_ "TextShow")
    # vfOrdCase (_S::S_ "TextReplace")
    # vfOrdCase (_S::S_ "ToMap")
    # vfOrd1Case (_S::S_ "Union")
    # vfOrdCase (_S::S_ "UsingHeaders")
    # vfOrdCase (_S::S_ "Var")
    # vfOrdCase (_S::S_ "With")
    ) e1 e2

instance eqExprRowVF' :: (Eq1 m, Eq1 m', Eq a, Eq b) => Eq (ExprRowVF' m m' a b) where
  eq = eq1
instance eq1ExprRowVF' :: (Eq1 m, Eq1 m', Eq a) => Eq1 (ExprRowVF' m m' a) where
  eq1 (ERVF' e1) (ERVF' e2) =
    ( VariantF.case_
    # vfEqCase (_S::S_ "Annot")
    # vfEqCase (_S::S_ "App")
    # vfEqCase (_S::S_ "Assert")
    # vfEqCase (_S::S_ "Bool")
    # vfEqCase (_S::S_ "BoolAnd")
    # vfEqCase (_S::S_ "BoolEQ")
    # vfEqCase (_S::S_ "BoolIf")
    # vfEqCase (_S::S_ "BoolLit")
    # vfEqCase (_S::S_ "BoolNE")
    # vfEqCase (_S::S_ "BoolOr")
    # vfEqCase (_S::S_ "Combine")
    # vfEqCase (_S::S_ "CombineTypes")
    # vfEqCase (_S::S_ "Const")
    # vfEqCase (_S::S_ "Double")
    # vfEqCase (_S::S_ "DoubleLit")
    # vfEqCase (_S::S_ "DoubleShow")
    # vfEqCase (_S::S_ "Embed")
    # vfEqCase (_S::S_ "Equivalent")
    # vfEqCase (_S::S_ "Field")
    # vfEqCase (_S::S_ "Hashed")
    # vfEqCase (_S::S_ "ImportAlt")
    # vfEqCase (_S::S_ "Integer")
    # vfEqCase (_S::S_ "IntegerLit")
    # vfEqCase (_S::S_ "IntegerShow")
    # vfEqCase (_S::S_ "IntegerToDouble")
    # vfEqCase (_S::S_ "IntegerNegate")
    # vfEqCase (_S::S_ "IntegerClamp")
    # vfEqCase (_S::S_ "Lam")
    # vfEqCase (_S::S_ "Let")
    # vfEqCase (_S::S_ "List")
    # vfEqCase (_S::S_ "ListAppend")
    # vfEqCase (_S::S_ "ListBuild")
    # vfEqCase (_S::S_ "ListFold")
    # vfEqCase (_S::S_ "ListHead")
    # vfEqCase (_S::S_ "ListIndexed")
    # vfEqCase (_S::S_ "ListLast")
    # vfEqCase (_S::S_ "ListLength")
    # vfEqCase (_S::S_ "ListLit")
    # vfEqCase (_S::S_ "ListReverse")
    # vfEqCase (_S::S_ "Merge")
    # vfEqCase (_S::S_ "Natural")
    # vfEqCase (_S::S_ "NaturalBuild")
    # vfEqCase (_S::S_ "NaturalEven")
    # vfEqCase (_S::S_ "NaturalFold")
    # vfEqCase (_S::S_ "NaturalIsZero")
    # vfEqCase (_S::S_ "NaturalLit")
    # vfEqCase (_S::S_ "NaturalOdd")
    # vfEqCase (_S::S_ "NaturalPlus")
    # vfEqCase (_S::S_ "NaturalShow")
    # vfEqCase (_S::S_ "NaturalTimes")
    # vfEqCase (_S::S_ "NaturalToInteger")
    # vfEqCase (_S::S_ "NaturalSubtract")
    # vfEqCase (_S::S_ "None")
    # vfEqCase (_S::S_ "Optional")
    # vfEqCase (_S::S_ "Pi")
    # vfEqCase (_S::S_ "Prefer")
    # vfEqCase (_S::S_ "Project")
    # vfEq1Case (_S::S_ "Record")
    # vfEqCase (_S::S_ "RecordCompletion")
    # vfEq1Case (_S::S_ "RecordLit")
    # vfEq1Case (_S::S_ "Some")
    # vfEqCase (_S::S_ "Text")
    # vfEqCase (_S::S_ "TextAppend")
    # vfEqCase (_S::S_ "TextLit")
    # vfEqCase (_S::S_ "TextShow")
    # vfEqCase (_S::S_ "TextReplace")
    # vfEqCase (_S::S_ "ToMap")
    # vfEq1Case (_S::S_ "Union")
    # vfEqCase (_S::S_ "UsingHeaders")
    # vfEqCase (_S::S_ "Var")
    # vfEqCase (_S::S_ "With")
    ) e1 e2

instance ordExprRowVF' :: (Ord1 m, Ord1 m', Ord a, Ord b) => Ord (ExprRowVF' m m' a b) where
  compare = compare1
instance ord1ExprRowVF' :: (Ord1 m, Ord1 m', Ord a) => Ord1 (ExprRowVF' m m' a) where
  compare1 (ERVF' e1) (ERVF' e2) =
    ( VariantF.case_
    # vfOrdCase (_S::S_ "Annot")
    # vfOrdCase (_S::S_ "App")
    # vfOrdCase (_S::S_ "Assert")
    # vfOrdCase (_S::S_ "Bool")
    # vfOrdCase (_S::S_ "BoolAnd")
    # vfOrdCase (_S::S_ "BoolEQ")
    # vfOrdCase (_S::S_ "BoolIf")
    # vfOrdCase (_S::S_ "BoolLit")
    # vfOrdCase (_S::S_ "BoolNE")
    # vfOrdCase (_S::S_ "BoolOr")
    # vfOrdCase (_S::S_ "Combine")
    # vfOrdCase (_S::S_ "CombineTypes")
    # vfOrdCase (_S::S_ "Const")
    # vfOrdCase (_S::S_ "Double")
    # vfOrdCase (_S::S_ "DoubleLit")
    # vfOrdCase (_S::S_ "DoubleShow")
    # vfOrdCase (_S::S_ "Embed")
    # vfOrdCase (_S::S_ "Equivalent")
    # vfOrdCase (_S::S_ "Field")
    # vfOrdCase (_S::S_ "Hashed")
    # vfOrdCase (_S::S_ "ImportAlt")
    # vfOrdCase (_S::S_ "Integer")
    # vfOrdCase (_S::S_ "IntegerLit")
    # vfOrdCase (_S::S_ "IntegerShow")
    # vfOrdCase (_S::S_ "IntegerToDouble")
    # vfOrdCase (_S::S_ "IntegerNegate")
    # vfOrdCase (_S::S_ "IntegerClamp")
    # vfOrdCase (_S::S_ "Lam")
    # vfOrdCase (_S::S_ "Let")
    # vfOrdCase (_S::S_ "List")
    # vfOrdCase (_S::S_ "ListAppend")
    # vfOrdCase (_S::S_ "ListBuild")
    # vfOrdCase (_S::S_ "ListFold")
    # vfOrdCase (_S::S_ "ListHead")
    # vfOrdCase (_S::S_ "ListIndexed")
    # vfOrdCase (_S::S_ "ListLast")
    # vfOrdCase (_S::S_ "ListLength")
    # vfOrdCase (_S::S_ "ListLit")
    # vfOrdCase (_S::S_ "ListReverse")
    # vfOrdCase (_S::S_ "Merge")
    # vfOrdCase (_S::S_ "Natural")
    # vfOrdCase (_S::S_ "NaturalBuild")
    # vfOrdCase (_S::S_ "NaturalEven")
    # vfOrdCase (_S::S_ "NaturalFold")
    # vfOrdCase (_S::S_ "NaturalIsZero")
    # vfOrdCase (_S::S_ "NaturalLit")
    # vfOrdCase (_S::S_ "NaturalOdd")
    # vfOrdCase (_S::S_ "NaturalPlus")
    # vfOrdCase (_S::S_ "NaturalShow")
    # vfOrdCase (_S::S_ "NaturalTimes")
    # vfOrdCase (_S::S_ "NaturalToInteger")
    # vfOrdCase (_S::S_ "NaturalSubtract")
    # vfOrdCase (_S::S_ "None")
    # vfOrdCase (_S::S_ "Optional")
    # vfOrdCase (_S::S_ "Pi")
    # vfOrdCase (_S::S_ "Prefer")
    # vfOrdCase (_S::S_ "Project")
    # vfOrd1Case (_S::S_ "Record")
    # vfOrdCase (_S::S_ "RecordCompletion")
    # vfOrd1Case (_S::S_ "RecordLit")
    # vfOrd1Case (_S::S_ "Some")
    # vfOrdCase (_S::S_ "Text")
    # vfOrdCase (_S::S_ "TextAppend")
    # vfOrdCase (_S::S_ "TextLit")
    # vfOrdCase (_S::S_ "TextShow")
    # vfOrdCase (_S::S_ "TextReplace")
    # vfOrdCase (_S::S_ "ToMap")
    # vfOrd1Case (_S::S_ "Union")
    # vfOrdCase (_S::S_ "UsingHeaders")
    # vfOrdCase (_S::S_ "Var")
    # vfOrdCase (_S::S_ "With")
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

newtype NoStrMap :: Type -> Type
newtype NoStrMap a = NoStrMap (ConstF.Const Void a)
derive instance newtypeNoStrMap :: Newtype (NoStrMap a) _
derive newtype instance functorNoStrMap :: Functor NoStrMap
derive newtype instance foldableNoStrMap :: Foldable NoStrMap
derive newtype instance traversableNoStrMap :: Traversable NoStrMap
instance functorWithIndexNoStrMap :: FunctorWithIndex i NoStrMap where
  mapWithIndex _ (NoStrMap void) = absurd $ unwrap $ void
instance foldableableWithIndexNoStrMap :: FoldableWithIndex i NoStrMap where
  foldMapWithIndex _ (NoStrMap void) = absurd $ unwrap $ void
  foldlWithIndex _ _ (NoStrMap void) = absurd $ unwrap $ void
  foldrWithIndex _ _ (NoStrMap void) = absurd $ unwrap $ void
instance traversableWithIndexNoStrMap :: TraversableWithIndex i NoStrMap where
  traverseWithIndex _ (NoStrMap void) = absurd $ unwrap $ void

type SimpleExpr = Expr NoStrMap Void

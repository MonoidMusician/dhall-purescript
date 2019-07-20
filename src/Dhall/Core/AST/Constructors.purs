module Dhall.Core.AST.Constructors where

import Data.Bifunctor (bimap)
import Data.Const as ConstF
import Data.Either (Either)
import Data.Functor.App (App(..))
import Data.Functor.Compose (Compose(..))
import Data.Functor.Product (Product(..), product)
import Data.Functor.Variant (VariantF)
import Data.Functor.Variant as VariantF
import Data.Identity (Identity(..))
import Data.Lens (Prism', prism', iso, only)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Maybe (Maybe(..))
import Data.Natural (Natural)
import Data.Newtype (unwrap)
import Data.Symbol (class IsSymbol, SProxy(..))
import Data.Tuple (Tuple(..), swap)
import Data.Variant.Internal (FProxy)
import Dhall.Core.AST.Types (Const(..), Expr, ExprLayerRow, Var, embedW, projectW)
import Dhall.Core.AST.Types.Basics (BindingBody(..), CONST, LetF(..), MergeF(..), Pair(..), TextLitF(..), Triplet(..), UNIT)
import Dhall.Core.StrMapIsh (class StrMapIsh)
import Dhall.Core.StrMapIsh as StrMapIsh
import Prelude (class Functor, Unit, const, identity, one, pure, unit, zero, (#), ($), (<<<))
import Prim.Row as Row

-- Constructors and prisms for each case of the AST

-- Pris(o)ms of the behemoth
_ExprF :: forall m a unused f k.
  Row.Cons k (FProxy f) unused (ExprLayerRow m a) =>
  IsSymbol k => Functor f =>
  SProxy k -> Prism' (Expr m a) (f (Expr m a))
_ExprF k = _E (_ExprFPrism k)

-- Convert a prism operating on VariantF ( ... ) Expr to one operating on Expr
_E :: forall f m a. Functor f =>
  Prism'
    (VariantF (ExprLayerRow m a) (Expr m a))
    (f (Expr m a)) ->
  Prism' (Expr m a) (f (Expr m a))
_E p = iso projectW embedW <<< p

type ExprFPrism r f = forall o. Prism' (VariantF r o) (f o)
_ExprFPrism :: forall r unused f k.
  Row.Cons k (FProxy f) unused r =>
  IsSymbol k => Functor f =>
  SProxy k -> ExprFPrism r f
_ExprFPrism k = prism' (VariantF.inj k)
  (VariantF.default Nothing # VariantF.on k Just)

_Expr :: forall m a unused v k.
  Row.Cons k (CONST v) unused (ExprLayerRow m a) =>
  IsSymbol k =>
  SProxy k -> Prism' (Expr m a) v
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

_BinOp :: forall m a unused k.
  Row.Cons k (FProxy Pair) unused (ExprLayerRow m a) =>
  IsSymbol k =>
  SProxy k -> Prism' (Expr m a) (Pair (Expr m a))
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

mkExprF :: forall m a unused f k.
  Row.Cons k (FProxy f) unused (ExprLayerRow m a) =>
  IsSymbol k => Functor f =>
  SProxy k -> f (Expr m a) -> Expr m a
mkExprF k v = embedW $ VariantF.inj k v

mkExpr :: forall m a unused v k.
  Row.Cons k (CONST v) unused (ExprLayerRow m a) =>
  IsSymbol k =>
  SProxy k -> v -> Expr m a
mkExpr k v = mkExprF k (ConstF.Const v)

mkBinOp :: forall m a unused k.
  Row.Cons k (FProxy Pair) unused (ExprLayerRow m a) =>
  IsSymbol k =>
  SProxy k -> Expr m a -> Expr m a -> Expr m a
mkBinOp k l r = mkExprF k
  (Pair l r)

mkConst :: forall m a. Const -> Expr m a
mkConst = mkExpr (SProxy :: SProxy "Const")

_Const :: forall r. ExprPrism ( "Const" :: CONST Const | r ) Const
_Const = _ExprPrism (SProxy :: SProxy "Const")

mkType :: forall m a. Expr m a
mkType = mkConst Type

mkKind :: forall m a. Expr m a
mkKind = mkConst Kind

mkSort :: forall m a. Expr m a
mkSort = mkConst Sort

mkVar :: forall m a. Var -> Expr m a
mkVar = mkExpr (SProxy :: SProxy "Var")

_Var :: forall r. ExprPrism ( "Var" :: CONST Var | r ) Var
_Var = _ExprPrism (SProxy :: SProxy "Var")

mkLam :: forall m a. String -> Expr m a -> Expr m a -> Expr m a
mkLam name ty expr = mkExprF (SProxy :: SProxy "Lam")
  (BindingBody name ty expr)

_Lam :: forall r o.
  Prism' (VariantF ( "Lam" :: FProxy BindingBody | r ) o)
  { var :: String, ty :: o, body :: o }
_Lam = _ExprFPrism (SProxy :: SProxy "Lam") <<< iso into outof where
  into (BindingBody var ty body) = { var, ty, body }
  outof { var, ty, body } = (BindingBody var ty body)

mkPi :: forall m a. String -> Expr m a -> Expr m a -> Expr m a
mkPi name ty expr = mkExprF (SProxy :: SProxy "Pi")
  (BindingBody name ty expr)

_Pi :: forall r o.
  Prism' (VariantF ( "Pi" :: FProxy BindingBody | r ) o)
  { var :: String, ty :: o, body :: o }
_Pi = _ExprFPrism (SProxy :: SProxy "Pi") <<< iso into outof where
  into (BindingBody var ty body) = { var, ty, body }
  outof { var, ty, body } = (BindingBody var ty body)

mkArrow :: forall m a. Expr m a -> Expr m a -> Expr m a
mkArrow = mkPi "_"

mkForall :: forall m a. String -> Expr m a -> Expr m a
mkForall name = mkPi name mkType

mkApp :: forall m a. Expr m a -> Expr m a -> Expr m a
mkApp fn arg = mkExprF (SProxy :: SProxy "App")
  (Pair fn arg)

_App :: forall r o.
  Prism' (VariantF ( "App" :: FProxy Pair | r ) o)
  { fn :: o, arg :: o }
_App = _ExprFPrism (SProxy :: SProxy "App") <<< iso into outof where
  into (Pair fn arg) = { fn, arg }
  outof { fn, arg } = Pair fn arg

mkLet :: forall m a. String -> Maybe (Expr m a) -> Expr m a -> Expr m a -> Expr m a
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

mkAnnot :: forall m a. Expr m a -> Expr m a -> Expr m a
mkAnnot val ty = mkExprF (SProxy :: SProxy "Annot")
  (Pair val ty)

_Annot :: forall r o.
  Prism' (VariantF ( "Annot" :: FProxy Pair | r ) o)
  { value :: o, ty :: o }
_Annot = _ExprFPrism (SProxy :: SProxy "Annot") <<< iso into outof where
  into (Pair value ty) = { value, ty }
  outof { value, ty } = Pair value ty

mkBool :: forall m a. Expr m a
mkBool = mkExpr (SProxy :: SProxy "Bool") unit

_Bool :: forall r. ExprPrism ( "Bool" :: UNIT | r ) Unit
_Bool = _ExprPrism (SProxy :: SProxy "Bool")

mkBoolLit :: forall m a. Boolean -> Expr m a
mkBoolLit = mkExpr (SProxy :: SProxy "BoolLit")

_BoolLit :: forall r. ExprPrism ( "BoolLit" :: CONST Boolean | r ) Boolean
_BoolLit = _ExprPrism (SProxy :: SProxy "BoolLit")

_BoolLit_True :: forall r. SimplePrism ( "BoolLit" :: CONST Boolean | r ) Unit
_BoolLit_True = _BoolLit <<< _Newtype <<< only true

_BoolLit_False :: forall r. SimplePrism ( "BoolLit" :: CONST Boolean | r ) Unit
_BoolLit_False = _BoolLit <<< _Newtype <<< only false

mkBoolAnd :: forall m a. Expr m a -> Expr m a -> Expr m a
mkBoolAnd = mkBinOp (SProxy :: SProxy "BoolAnd")

_BoolAnd :: forall r. BinOpPrism ( "BoolAnd" :: FProxy Pair | r )
_BoolAnd = _BinOpPrism (SProxy :: SProxy "BoolAnd")

mkBoolOr :: forall m a. Expr m a -> Expr m a -> Expr m a
mkBoolOr = mkBinOp (SProxy :: SProxy "BoolOr")

_BoolOr :: forall r. BinOpPrism ( "BoolOr" :: FProxy Pair | r )
_BoolOr = _BinOpPrism (SProxy :: SProxy "BoolOr")

mkBoolEQ :: forall m a. Expr m a -> Expr m a -> Expr m a
mkBoolEQ = mkBinOp (SProxy :: SProxy "BoolEQ")

_BoolEQ :: forall r. BinOpPrism ( "BoolEQ" :: FProxy Pair | r )
_BoolEQ = _BinOpPrism (SProxy :: SProxy "BoolEQ")

mkBoolNE :: forall m a. Expr m a -> Expr m a -> Expr m a
mkBoolNE = mkBinOp (SProxy :: SProxy "BoolNE")

_BoolNE :: forall r. BinOpPrism ( "BoolNE" :: FProxy Pair | r )
_BoolNE = _BinOpPrism (SProxy :: SProxy "BoolNE")

mkBoolIf :: forall m a. Expr m a -> Expr m a -> Expr m a -> Expr m a
mkBoolIf cond t f = mkExprF (SProxy :: SProxy "BoolIf")
  (Triplet cond t f)

_BoolIf :: forall r. ExprFPrism ( "BoolIf" :: FProxy Triplet | r ) Triplet
_BoolIf = _ExprFPrism (SProxy :: SProxy "BoolIf")

mkNatural :: forall m a. Expr m a
mkNatural = mkExpr (SProxy :: SProxy "Natural") unit

_Natural :: forall r. ExprPrism ( "Natural" :: UNIT | r ) Unit
_Natural = _ExprPrism (SProxy :: SProxy "Natural")

mkNaturalLit :: forall m a. Natural -> Expr m a
mkNaturalLit = mkExpr (SProxy :: SProxy "NaturalLit")

_NaturalLit :: forall r. ExprPrism ( "NaturalLit" :: CONST Natural | r ) Natural
_NaturalLit = _ExprPrism (SProxy :: SProxy "NaturalLit")

_NaturalLit_0 :: forall r. SimplePrism ( "NaturalLit" :: CONST Natural | r ) Unit
_NaturalLit_0 = _NaturalLit <<< _Newtype <<< only zero

_NaturalLit_1 :: forall r. SimplePrism ( "NaturalLit" :: CONST Natural | r ) Unit
_NaturalLit_1 = _NaturalLit <<< _Newtype <<< only one

mkNaturalFold :: forall m a. Expr m a
mkNaturalFold = mkExpr (SProxy :: SProxy "NaturalFold") unit

_NaturalFold :: forall r. ExprPrism ( "NaturalFold" :: UNIT | r ) Unit
_NaturalFold = _ExprPrism (SProxy :: SProxy "NaturalFold")

mkNaturalBuild :: forall m a. Expr m a
mkNaturalBuild = mkExpr (SProxy :: SProxy "NaturalBuild") unit

_NaturalBuild :: forall r. ExprPrism ( "NaturalBuild" :: UNIT | r ) Unit
_NaturalBuild = _ExprPrism (SProxy :: SProxy "NaturalBuild")

mkNaturalIsZero :: forall m a. Expr m a
mkNaturalIsZero = mkExpr (SProxy :: SProxy "NaturalIsZero") unit

_NaturalIsZero :: forall r. ExprPrism ( "NaturalIsZero" :: UNIT | r ) Unit
_NaturalIsZero = _ExprPrism (SProxy :: SProxy "NaturalIsZero")

mkNaturalEven :: forall m a. Expr m a
mkNaturalEven = mkExpr (SProxy :: SProxy "NaturalEven") unit

_NaturalEven :: forall r. ExprPrism ( "NaturalEven" :: UNIT | r ) Unit
_NaturalEven = _ExprPrism (SProxy :: SProxy "NaturalEven")

mkNaturalOdd :: forall m a. Expr m a
mkNaturalOdd = mkExpr (SProxy :: SProxy "NaturalOdd") unit

_NaturalOdd :: forall r. ExprPrism ( "NaturalOdd" :: UNIT | r ) Unit
_NaturalOdd = _ExprPrism (SProxy :: SProxy "NaturalOdd")

mkNaturalToInteger :: forall m a. Expr m a
mkNaturalToInteger = mkExpr (SProxy :: SProxy "NaturalToInteger") unit

_NaturalToInteger :: forall r. ExprPrism ( "NaturalToInteger" :: UNIT | r ) Unit
_NaturalToInteger = _ExprPrism (SProxy :: SProxy "NaturalToInteger")

mkNaturalShow :: forall m a. Expr m a
mkNaturalShow = mkExpr (SProxy :: SProxy "NaturalShow") unit

_NaturalShow :: forall r. ExprPrism ( "NaturalShow" :: UNIT | r ) Unit
_NaturalShow = _ExprPrism (SProxy :: SProxy "NaturalShow")

mkNaturalPlus :: forall m a. Expr m a -> Expr m a -> Expr m a
mkNaturalPlus = mkBinOp (SProxy :: SProxy "NaturalPlus")

_NaturalPlus :: forall r. BinOpPrism ( "NaturalPlus" :: FProxy Pair | r )
_NaturalPlus = _BinOpPrism (SProxy :: SProxy "NaturalPlus")

mkNaturalTimes :: forall m a. Expr m a -> Expr m a -> Expr m a
mkNaturalTimes = mkBinOp (SProxy :: SProxy "NaturalTimes")

_NaturalTimes :: forall r. BinOpPrism ( "NaturalTimes" :: FProxy Pair | r )
_NaturalTimes = _BinOpPrism (SProxy :: SProxy "NaturalTimes")

mkInteger :: forall m a. Expr m a
mkInteger = mkExpr (SProxy :: SProxy "Integer") unit

_Integer :: forall r. ExprPrism ( "Integer" :: UNIT | r ) Unit
_Integer = _ExprPrism (SProxy :: SProxy "Integer")

mkIntegerLit :: forall m a. Int -> Expr m a
mkIntegerLit = mkExpr (SProxy :: SProxy "IntegerLit")

_IntegerLit :: forall r. ExprPrism ( "IntegerLit" :: CONST Int | r ) Int
_IntegerLit = _ExprPrism (SProxy :: SProxy "IntegerLit")

mkIntegerShow :: forall m a. Expr m a
mkIntegerShow = mkExpr (SProxy :: SProxy "IntegerShow") unit

_IntegerShow :: forall r. ExprPrism ( "IntegerShow" :: UNIT | r ) Unit
_IntegerShow = _ExprPrism (SProxy :: SProxy "IntegerShow")

mkIntegerToDouble :: forall m a. Expr m a
mkIntegerToDouble = mkExpr (SProxy :: SProxy "IntegerToDouble") unit

_IntegerToDouble :: forall r. ExprPrism ( "IntegerToDouble" :: UNIT | r ) Unit
_IntegerToDouble = _ExprPrism (SProxy :: SProxy "IntegerToDouble")

mkDouble :: forall m a. Expr m a
mkDouble = mkExpr (SProxy :: SProxy "Double") unit

_Double :: forall r. ExprPrism ( "Double" :: UNIT | r ) Unit
_Double = _ExprPrism (SProxy :: SProxy "Double")

mkDoubleLit :: forall m a. Number -> Expr m a
mkDoubleLit = mkExpr (SProxy :: SProxy "DoubleLit")

_DoubleLit :: forall r. ExprPrism ( "DoubleLit" :: CONST Number | r ) Number
_DoubleLit = _ExprPrism (SProxy :: SProxy "DoubleLit")

mkDoubleShow :: forall m a. Expr m a
mkDoubleShow = mkExpr (SProxy :: SProxy "DoubleShow") unit

_DoubleShow :: forall r. ExprPrism ( "DoubleShow" :: UNIT | r ) Unit
_DoubleShow = _ExprPrism (SProxy :: SProxy "DoubleShow")

mkText :: forall m a. Expr m a
mkText = mkExpr (SProxy :: SProxy "Text") unit

_Text :: forall r. ExprPrism ( "Text" :: UNIT | r ) Unit
_Text = _ExprPrism (SProxy :: SProxy "Text")

mkTextLit :: forall m a. TextLitF (Expr m a) -> Expr m a
mkTextLit = mkExprF (SProxy :: SProxy "TextLit")

_TextLit :: forall r. ExprFPrism ( "TextLit" :: FProxy TextLitF | r ) TextLitF
_TextLit = _ExprFPrism (SProxy :: SProxy "TextLit")

_TextLit_empty :: forall r o. Prism' (VariantF ( "TextLit" :: FProxy TextLitF | r ) o) Unit
_TextLit_empty = _TextLit <<< prism' (const (TextLit ""))
  case _ of
    TextLit "" -> Just unit
    _ -> Nothing

_TextLit_single :: forall r o. Prism' (VariantF ( "TextLit" :: FProxy TextLitF | r ) o) String
_TextLit_single = _TextLit <<< prism' TextLit
  case _ of
    TextLit s -> Just s
    _ -> Nothing

mkTextAppend :: forall m a. Expr m a -> Expr m a -> Expr m a
mkTextAppend = mkBinOp (SProxy :: SProxy "TextAppend")

_TextAppend :: forall r. BinOpPrism ( "TextAppend" :: FProxy Pair | r )
_TextAppend = _BinOpPrism (SProxy :: SProxy "TextAppend")

mkList :: forall m a. Expr m a
mkList = mkExpr (SProxy :: SProxy "List") unit

_List :: forall r. ExprPrism ( "List" :: UNIT | r ) Unit
_List = _ExprPrism (SProxy :: SProxy "List")

mkListLit :: forall m a. Maybe (Expr m a) -> Array (Expr m a) -> Expr m a
mkListLit ty lit = mkExprF (SProxy :: SProxy "ListLit")
  (product ty lit)

_ListLit :: forall r o.
  Prism' (VariantF ( "ListLit" :: FProxy (Product Maybe Array) | r ) o)
  { ty :: Maybe o, values :: Array o }
_ListLit = _ExprFPrism (SProxy :: SProxy "ListLit") <<< _Newtype <<< iso into outof where
  into (Tuple ty values) = { ty, values }
  outof { ty, values } = Tuple ty values

mkListAppend :: forall m a. Expr m a -> Expr m a -> Expr m a
mkListAppend = mkBinOp (SProxy :: SProxy "ListAppend")

_ListAppend :: forall r. BinOpPrism ( "ListAppend" :: FProxy Pair | r )
_ListAppend = _BinOpPrism (SProxy :: SProxy "ListAppend")

mkListFold :: forall m a. Expr m a
mkListFold = mkExpr (SProxy :: SProxy "ListFold") unit

_ListFold :: forall r. ExprPrism ( "ListFold" :: UNIT | r ) Unit
_ListFold = _ExprPrism (SProxy :: SProxy "ListFold")

mkListBuild :: forall m a. Expr m a
mkListBuild = mkExpr (SProxy :: SProxy "ListBuild") unit

_ListBuild :: forall r. ExprPrism ( "ListBuild" :: UNIT | r ) Unit
_ListBuild = _ExprPrism (SProxy :: SProxy "ListBuild")

mkListLength :: forall m a. Expr m a
mkListLength = mkExpr (SProxy :: SProxy "ListLength") unit

_ListLength :: forall r. ExprPrism ( "ListLength" :: UNIT | r ) Unit
_ListLength = _ExprPrism (SProxy :: SProxy "ListLength")

mkListHead :: forall m a. Expr m a
mkListHead = mkExpr (SProxy :: SProxy "ListHead") unit

_ListHead :: forall r. ExprPrism ( "ListHead" :: UNIT | r ) Unit
_ListHead = _ExprPrism (SProxy :: SProxy "ListHead")

mkListLast :: forall m a. Expr m a
mkListLast = mkExpr (SProxy :: SProxy "ListLast") unit

_ListLast :: forall r. ExprPrism ( "ListLast" :: UNIT | r ) Unit
_ListLast = _ExprPrism (SProxy :: SProxy "ListLast")

mkListIndexed :: forall m a. Expr m a
mkListIndexed = mkExpr (SProxy :: SProxy "ListIndexed") unit

_ListIndexed :: forall r. ExprPrism ( "ListIndexed" :: UNIT | r ) Unit
_ListIndexed = _ExprPrism (SProxy :: SProxy "ListIndexed")

mkListReverse :: forall m a. Expr m a
mkListReverse = mkExpr (SProxy :: SProxy "ListReverse") unit

_ListReverse :: forall r. ExprPrism ( "ListReverse" :: UNIT | r ) Unit
_ListReverse = _ExprPrism (SProxy :: SProxy "ListReverse")

mkOptional :: forall m a. Expr m a
mkOptional = mkExpr (SProxy :: SProxy "Optional") unit

_Optional :: forall r. ExprPrism ( "Optional" :: UNIT | r ) Unit
_Optional = _ExprPrism (SProxy :: SProxy "Optional")

mkSome :: forall m a. Expr m a -> Expr m a
mkSome val = mkExprF (SProxy :: SProxy "Some")
  (Identity val)

_Some :: forall r o.
  Prism' (VariantF ( "Some" :: FProxy Identity | r ) o) o
_Some = _ExprFPrism (SProxy :: SProxy "Some") <<< _Newtype

mkNone :: forall m a. Expr m a
mkNone = mkExpr (SProxy :: SProxy "None") unit

_None :: forall r. ExprPrism ( "None" :: UNIT | r ) Unit
_None = _ExprPrism (SProxy :: SProxy "None")

mkOptionalFold :: forall m a. Expr m a
mkOptionalFold = mkExpr (SProxy :: SProxy "OptionalFold") unit

_OptionalFold :: forall r. ExprPrism ( "OptionalFold" :: UNIT | r ) Unit
_OptionalFold = _ExprPrism (SProxy :: SProxy "OptionalFold")

mkOptionalBuild :: forall m a. Expr m a
mkOptionalBuild = mkExpr (SProxy :: SProxy "OptionalBuild") unit

_OptionalBuild :: forall r. ExprPrism ( "OptionalBuild" :: UNIT | r ) Unit
_OptionalBuild = _ExprPrism (SProxy :: SProxy "OptionalBuild")

mkRecord :: forall m a. Functor m => m (Expr m a) -> Expr m a
mkRecord = mkExprF (SProxy :: SProxy "Record")

_Record :: forall r m. Functor m => ExprFPrism
  ( "Record" :: FProxy m | r ) m
_Record = _ExprFPrism (SProxy :: SProxy "Record")

_Record_empty :: forall r o m. StrMapIsh m =>
  Prism' (VariantF ( "Record" :: FProxy m | r ) o) Unit
_Record_empty = _Record <<< StrMapIsh._Empty

mkRecordLit :: forall a m. Functor m => m (Expr m a) -> Expr m a
mkRecordLit = mkExprF (SProxy :: SProxy "RecordLit")

_RecordLit :: forall r m. Functor m => ExprFPrism
  ( "RecordLit" :: FProxy m | r ) m
_RecordLit = _ExprFPrism (SProxy :: SProxy "RecordLit")

_RecordLit_empty :: forall r o m. StrMapIsh m =>
  Prism' (VariantF ( "RecordLit" :: FProxy m | r ) o) Unit
_RecordLit_empty = _RecordLit <<< StrMapIsh._Empty

mkUnion :: forall m a. Functor m => m (Maybe (Expr m a)) -> Expr m a
mkUnion = mkExprF (SProxy :: SProxy "Union") <<< Compose

_Union :: forall r m. Functor m => ExprFPrism ( "Union" :: FProxy (Compose m Maybe) | r ) (Compose m Maybe)
_Union = _ExprFPrism (SProxy :: SProxy "Union")

_Union_empty :: forall r o m. StrMapIsh m =>
  Prism' (VariantF ( "Union" :: FProxy (Compose m Maybe) | r ) o) Unit
_Union_empty = _Union <<< _Newtype <<< StrMapIsh._Empty

mkUnionLit :: forall m a. Functor m => String -> Expr m a -> m (Expr m a) -> Expr m a
mkUnionLit name value others = mkExprF (SProxy :: SProxy "UnionLit")
  (product (Tuple name value) others)

_UnionLit :: forall r o m. Functor m => Prism'
  (VariantF ( "UnionLit" :: FProxy (Product (Tuple String) m) | r ) o)
  { label :: String, value :: o, tys :: m o }
_UnionLit = _ExprFPrism (SProxy :: SProxy "UnionLit") <<< _Newtype <<< iso into outof where
  into (Tuple (Tuple label value) tys) = { label, value, tys }
  outof { label, value, tys } = Tuple (Tuple label value) tys

mkCombine :: forall m a. Expr m a -> Expr m a -> Expr m a
mkCombine = mkBinOp (SProxy :: SProxy "Combine")

_Combine :: forall r. BinOpPrism ( "Combine" :: FProxy Pair | r )
_Combine = _BinOpPrism (SProxy :: SProxy "Combine")

mkCombineTypes :: forall m a. Expr m a -> Expr m a -> Expr m a
mkCombineTypes = mkBinOp (SProxy :: SProxy "CombineTypes")

_CombineTypes :: forall r. BinOpPrism ( "CombineTypes" :: FProxy Pair | r )
_CombineTypes = _BinOpPrism (SProxy :: SProxy "CombineTypes")

mkPrefer :: forall m a. Expr m a -> Expr m a -> Expr m a
mkPrefer = mkBinOp (SProxy :: SProxy "Prefer")

_Prefer :: forall r. BinOpPrism ( "Prefer" :: FProxy Pair | r )
_Prefer = _BinOpPrism (SProxy :: SProxy "Prefer")

mkMerge :: forall m a. Expr m a -> Expr m a -> Maybe (Expr m a) -> Expr m a
mkMerge x y t = mkExprF (SProxy :: SProxy "Merge")
  (MergeF x y t)

_Merge :: forall r. ExprFPrism ( "Merge" :: FProxy MergeF | r ) MergeF
_Merge = _ExprFPrism (SProxy :: SProxy "Merge")

mkToMap :: forall m a. Expr m a -> Maybe (Expr m a) -> Expr m a
mkToMap x t = mkExprF (SProxy :: SProxy "ToMap")
  (Product (Tuple (Identity x) t))

_ToMap :: forall r. ExprFPrism ( "ToMap" :: FProxy (Product Identity Maybe) | r ) (Product Identity Maybe)
_ToMap = _ExprFPrism (SProxy :: SProxy "ToMap")

mkField :: forall m a. Expr m a -> String -> Expr m a
mkField expr field = mkExprF (SProxy :: SProxy "Field")
  (Tuple field expr)

_Field :: forall r o. Prism'
  (VariantF ( "Field" :: FProxy (Tuple String) | r ) o)
  (Tuple o String)
_Field = _ExprFPrism (SProxy :: SProxy "Field") <<< iso swap swap

mkProject :: forall m a. Expr m a -> Either (m Unit) (Expr m a) -> Expr m a
mkProject expr fields = mkExprF (SProxy :: SProxy "Project")
  (Product (Tuple (pure expr) (bimap App identity fields)))

_Project :: forall m r o. Prism'
  (VariantF ( "Project" :: FProxy (Product Identity (Either (App m Unit))) | r ) o)
  (Tuple o (Either (m Unit) o))
_Project = _ExprFPrism (SProxy :: SProxy "Project") <<< iso
  do \(Product (Tuple (Identity o) e)) -> Tuple o (bimap unwrap identity e)
  do \(Tuple o e) -> Product (Tuple (Identity o) (bimap App identity e))

mkImportAlt :: forall m a. Expr m a -> Expr m a -> Expr m a
mkImportAlt = mkBinOp (SProxy :: SProxy "ImportAlt")

_ImportAlt :: forall r. BinOpPrism ( "ImportAlt" :: FProxy Pair | r )
_ImportAlt = _BinOpPrism (SProxy :: SProxy "ImportAlt")

mkEmbed :: forall m a. a -> Expr m a
mkEmbed = pure

_Embed :: forall a r. ExprPrism ( "Embed" :: CONST a | r ) a
_Embed = _ExprPrism (SProxy :: SProxy "Embed")

module Dhall.Core.AST.Constructors where

import Prelude (class Functor, Unit, const, one, pure, unit, zero, (#), ($), (<<<))

import Data.Const as ConstF
import Data.Functor.Product (Product, product)
import Data.Functor.Variant (VariantF)
import Data.Functor.Variant as VariantF
import Data.Identity (Identity(..))
import Data.Lens (Prism', prism', iso, only)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Maybe (Maybe(..))
import Data.Natural (Natural)
import Data.Symbol (class IsSymbol, SProxy(..))
import Data.Tuple (Tuple(..), swap)
import Data.Variant.Internal (FProxy)
import Dhall.Core.AST.Types.Basics (BindingBody(..), CONST, LetF(..), MergeF(..), Pair(..), TextLitF(..), Triplet(..), UNIT)
import Dhall.Core.AST.Types (Const, Expr, ExprLayerRow, Var, embedW, projectW)
import Dhall.Core.StrMapIsh (class StrMapIsh)
import Dhall.Core.StrMapIsh as StrMapIsh
import Prim.Row as Row

-- Constructors and prisms for each case of the AST

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
  (BindingBody name ty expr)

_Lam :: forall r o.
  Prism' (VariantF ( "Lam" :: FProxy BindingBody | r ) o)
  { var :: String, ty :: o, body :: o }
_Lam = _ExprFPrism (SProxy :: SProxy "Lam") <<< iso into outof where
  into (BindingBody var ty body) = { var, ty, body }
  outof { var, ty, body } = (BindingBody var ty body)

mkPi :: forall m s a. String -> Expr m s a -> Expr m s a -> Expr m s a
mkPi name ty expr = mkExprF (SProxy :: SProxy "Pi")
  (BindingBody name ty expr)

_Pi :: forall r o.
  Prism' (VariantF ( "Pi" :: FProxy BindingBody | r ) o)
  { var :: String, ty :: o, body :: o }
_Pi = _ExprFPrism (SProxy :: SProxy "Pi") <<< iso into outof where
  into (BindingBody var ty body) = { var, ty, body }
  outof { var, ty, body } = (BindingBody var ty body)

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

mkSome :: forall m s a. Expr m s a -> Expr m s a
mkSome val = mkExprF (SProxy :: SProxy "Some")
  (Identity val)

_Some :: forall r o.
  Prism' (VariantF ( "Some" :: FProxy Identity | r ) o) o
_Some = _ExprFPrism (SProxy :: SProxy "Some") <<< _Newtype

mkNone :: forall m s a. Expr m s a
mkNone = mkExpr (SProxy :: SProxy "None") unit

_None :: forall r. ExprPrism ( "None" :: UNIT | r ) Unit
_None = _ExprPrism (SProxy :: SProxy "None")

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

mkProject :: forall m s a. Expr m s a -> m Unit -> Expr m s a
mkProject expr fields = mkExprF (SProxy :: SProxy "Project")
  (Tuple fields expr)

_Project :: forall m r o. Prism'
  (VariantF ( "Project" :: FProxy (Tuple (m Unit)) | r ) o)
  (Tuple o (m Unit))
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

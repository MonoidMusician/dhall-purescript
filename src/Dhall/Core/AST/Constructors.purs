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
import Data.Symbol (class IsSymbol, SProxy)
import Data.Tuple (Tuple(..), swap)
import Data.Variant.Internal (FProxy)
import Dhall.Core.AST.Types (Const(..), Expr, ExprLayerRow, Var, embedW, projectW)
import Dhall.Core.AST.Types.Basics (_S, S_, BindingBody(..), CONST, LetF(..), MergeF(..), Pair(..), TextLitF(..), Triplet(..), UNIT)
import Dhall.Map (class MapLike)
import Dhall.Map as Dhall.Map
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
mkConst = mkExpr (_S::S_ "Const")

_Const :: forall r. ExprPrism ( "Const" :: CONST Const | r ) Const
_Const = _ExprPrism (_S::S_ "Const")

mkType :: forall m a. Expr m a
mkType = mkConst Type

mkKind :: forall m a. Expr m a
mkKind = mkConst Kind

mkSort :: forall m a. Expr m a
mkSort = mkConst Sort

mkVar :: forall m a. Var -> Expr m a
mkVar = mkExpr (_S::S_ "Var")

_Var :: forall r. ExprPrism ( "Var" :: CONST Var | r ) Var
_Var = _ExprPrism (_S::S_ "Var")

mkLam :: forall m a. String -> Expr m a -> Expr m a -> Expr m a
mkLam name ty expr = mkExprF (_S::S_ "Lam")
  (BindingBody name ty expr)

_Lam :: forall r o.
  Prism' (VariantF ( "Lam" :: FProxy BindingBody | r ) o)
  { var :: String, ty :: o, body :: o }
_Lam = _ExprFPrism (_S::S_ "Lam") <<< iso into outof where
  into (BindingBody var ty body) = { var, ty, body }
  outof { var, ty, body } = (BindingBody var ty body)

mkPi :: forall m a. String -> Expr m a -> Expr m a -> Expr m a
mkPi name ty expr = mkExprF (_S::S_ "Pi")
  (BindingBody name ty expr)

_Pi :: forall r o.
  Prism' (VariantF ( "Pi" :: FProxy BindingBody | r ) o)
  { var :: String, ty :: o, body :: o }
_Pi = _ExprFPrism (_S::S_ "Pi") <<< iso into outof where
  into (BindingBody var ty body) = { var, ty, body }
  outof { var, ty, body } = (BindingBody var ty body)

mkArrow :: forall m a. Expr m a -> Expr m a -> Expr m a
mkArrow = mkPi "_"

mkForall :: forall m a. String -> Expr m a -> Expr m a
mkForall name = mkPi name mkType

mkApp :: forall m a. Expr m a -> Expr m a -> Expr m a
mkApp fn arg = mkExprF (_S::S_ "App")
  (Pair fn arg)

_App :: forall r o.
  Prism' (VariantF ( "App" :: FProxy Pair | r ) o)
  { fn :: o, arg :: o }
_App = _ExprFPrism (_S::S_ "App") <<< iso into outof where
  into (Pair fn arg) = { fn, arg }
  outof { fn, arg } = Pair fn arg

mkLet :: forall m a. String -> Maybe (Expr m a) -> Expr m a -> Expr m a -> Expr m a
mkLet name ty val expr = mkExprF (_S::S_ "Let")
  (LetF name ty val expr)

_Let :: forall r o.
  Prism' (VariantF ( "Let" :: FProxy LetF | r ) o)
  { var :: String
  , ty :: Maybe o
  , value :: o
  , body :: o
  }
_Let = _ExprFPrism (_S::S_ "Let") <<< iso into outof where
  into (LetF var ty value body) = { var, ty, value, body }
  outof { var, ty, value, body } = LetF var ty value body

mkAnnot :: forall m a. Expr m a -> Expr m a -> Expr m a
mkAnnot val ty = mkExprF (_S::S_ "Annot")
  (Pair val ty)

_Annot :: forall r o.
  Prism' (VariantF ( "Annot" :: FProxy Pair | r ) o)
  { value :: o, ty :: o }
_Annot = _ExprFPrism (_S::S_ "Annot") <<< iso into outof where
  into (Pair value ty) = { value, ty }
  outof { value, ty } = Pair value ty

mkBool :: forall m a. Expr m a
mkBool = mkExpr (_S::S_ "Bool") unit

_Bool :: forall r. ExprPrism ( "Bool" :: UNIT | r ) Unit
_Bool = _ExprPrism (_S::S_ "Bool")

mkBoolLit :: forall m a. Boolean -> Expr m a
mkBoolLit = mkExpr (_S::S_ "BoolLit")

_BoolLit :: forall r. ExprPrism ( "BoolLit" :: CONST Boolean | r ) Boolean
_BoolLit = _ExprPrism (_S::S_ "BoolLit")

_BoolLit_True :: forall r. SimplePrism ( "BoolLit" :: CONST Boolean | r ) Unit
_BoolLit_True = _BoolLit <<< _Newtype <<< only true

_BoolLit_False :: forall r. SimplePrism ( "BoolLit" :: CONST Boolean | r ) Unit
_BoolLit_False = _BoolLit <<< _Newtype <<< only false

mkBoolAnd :: forall m a. Expr m a -> Expr m a -> Expr m a
mkBoolAnd = mkBinOp (_S::S_ "BoolAnd")

_BoolAnd :: forall r. BinOpPrism ( "BoolAnd" :: FProxy Pair | r )
_BoolAnd = _BinOpPrism (_S::S_ "BoolAnd")

mkBoolOr :: forall m a. Expr m a -> Expr m a -> Expr m a
mkBoolOr = mkBinOp (_S::S_ "BoolOr")

_BoolOr :: forall r. BinOpPrism ( "BoolOr" :: FProxy Pair | r )
_BoolOr = _BinOpPrism (_S::S_ "BoolOr")

mkBoolEQ :: forall m a. Expr m a -> Expr m a -> Expr m a
mkBoolEQ = mkBinOp (_S::S_ "BoolEQ")

_BoolEQ :: forall r. BinOpPrism ( "BoolEQ" :: FProxy Pair | r )
_BoolEQ = _BinOpPrism (_S::S_ "BoolEQ")

mkBoolNE :: forall m a. Expr m a -> Expr m a -> Expr m a
mkBoolNE = mkBinOp (_S::S_ "BoolNE")

_BoolNE :: forall r. BinOpPrism ( "BoolNE" :: FProxy Pair | r )
_BoolNE = _BinOpPrism (_S::S_ "BoolNE")

mkBoolIf :: forall m a. Expr m a -> Expr m a -> Expr m a -> Expr m a
mkBoolIf cond t f = mkExprF (_S::S_ "BoolIf")
  (Triplet cond t f)

_BoolIf :: forall r. ExprFPrism ( "BoolIf" :: FProxy Triplet | r ) Triplet
_BoolIf = _ExprFPrism (_S::S_ "BoolIf")

mkNatural :: forall m a. Expr m a
mkNatural = mkExpr (_S::S_ "Natural") unit

_Natural :: forall r. ExprPrism ( "Natural" :: UNIT | r ) Unit
_Natural = _ExprPrism (_S::S_ "Natural")

mkNaturalLit :: forall m a. Natural -> Expr m a
mkNaturalLit = mkExpr (_S::S_ "NaturalLit")

_NaturalLit :: forall r. ExprPrism ( "NaturalLit" :: CONST Natural | r ) Natural
_NaturalLit = _ExprPrism (_S::S_ "NaturalLit")

_NaturalLit_0 :: forall r. SimplePrism ( "NaturalLit" :: CONST Natural | r ) Unit
_NaturalLit_0 = _NaturalLit <<< _Newtype <<< only zero

_NaturalLit_1 :: forall r. SimplePrism ( "NaturalLit" :: CONST Natural | r ) Unit
_NaturalLit_1 = _NaturalLit <<< _Newtype <<< only one

mkNaturalFold :: forall m a. Expr m a
mkNaturalFold = mkExpr (_S::S_ "NaturalFold") unit

_NaturalFold :: forall r. ExprPrism ( "NaturalFold" :: UNIT | r ) Unit
_NaturalFold = _ExprPrism (_S::S_ "NaturalFold")

mkNaturalBuild :: forall m a. Expr m a
mkNaturalBuild = mkExpr (_S::S_ "NaturalBuild") unit

_NaturalBuild :: forall r. ExprPrism ( "NaturalBuild" :: UNIT | r ) Unit
_NaturalBuild = _ExprPrism (_S::S_ "NaturalBuild")

mkNaturalIsZero :: forall m a. Expr m a
mkNaturalIsZero = mkExpr (_S::S_ "NaturalIsZero") unit

_NaturalIsZero :: forall r. ExprPrism ( "NaturalIsZero" :: UNIT | r ) Unit
_NaturalIsZero = _ExprPrism (_S::S_ "NaturalIsZero")

mkNaturalEven :: forall m a. Expr m a
mkNaturalEven = mkExpr (_S::S_ "NaturalEven") unit

_NaturalEven :: forall r. ExprPrism ( "NaturalEven" :: UNIT | r ) Unit
_NaturalEven = _ExprPrism (_S::S_ "NaturalEven")

mkNaturalOdd :: forall m a. Expr m a
mkNaturalOdd = mkExpr (_S::S_ "NaturalOdd") unit

_NaturalOdd :: forall r. ExprPrism ( "NaturalOdd" :: UNIT | r ) Unit
_NaturalOdd = _ExprPrism (_S::S_ "NaturalOdd")

mkNaturalToInteger :: forall m a. Expr m a
mkNaturalToInteger = mkExpr (_S::S_ "NaturalToInteger") unit

_NaturalToInteger :: forall r. ExprPrism ( "NaturalToInteger" :: UNIT | r ) Unit
_NaturalToInteger = _ExprPrism (_S::S_ "NaturalToInteger")

mkNaturalShow :: forall m a. Expr m a
mkNaturalShow = mkExpr (_S::S_ "NaturalShow") unit

_NaturalShow :: forall r. ExprPrism ( "NaturalShow" :: UNIT | r ) Unit
_NaturalShow = _ExprPrism (_S::S_ "NaturalShow")

mkNaturalSubtract :: forall m a. Expr m a
mkNaturalSubtract = mkExpr (_S::S_ "NaturalSubtract") unit

_NaturalSubtract :: forall r. ExprPrism ( "NaturalSubtract" :: UNIT | r ) Unit
_NaturalSubtract = _ExprPrism (_S::S_ "NaturalSubtract")

mkNaturalPlus :: forall m a. Expr m a -> Expr m a -> Expr m a
mkNaturalPlus = mkBinOp (_S::S_ "NaturalPlus")

_NaturalPlus :: forall r. BinOpPrism ( "NaturalPlus" :: FProxy Pair | r )
_NaturalPlus = _BinOpPrism (_S::S_ "NaturalPlus")

mkNaturalTimes :: forall m a. Expr m a -> Expr m a -> Expr m a
mkNaturalTimes = mkBinOp (_S::S_ "NaturalTimes")

_NaturalTimes :: forall r. BinOpPrism ( "NaturalTimes" :: FProxy Pair | r )
_NaturalTimes = _BinOpPrism (_S::S_ "NaturalTimes")

mkInteger :: forall m a. Expr m a
mkInteger = mkExpr (_S::S_ "Integer") unit

_Integer :: forall r. ExprPrism ( "Integer" :: UNIT | r ) Unit
_Integer = _ExprPrism (_S::S_ "Integer")

mkIntegerLit :: forall m a. Int -> Expr m a
mkIntegerLit = mkExpr (_S::S_ "IntegerLit")

_IntegerLit :: forall r. ExprPrism ( "IntegerLit" :: CONST Int | r ) Int
_IntegerLit = _ExprPrism (_S::S_ "IntegerLit")

mkIntegerShow :: forall m a. Expr m a
mkIntegerShow = mkExpr (_S::S_ "IntegerShow") unit

_IntegerShow :: forall r. ExprPrism ( "IntegerShow" :: UNIT | r ) Unit
_IntegerShow = _ExprPrism (_S::S_ "IntegerShow")

mkIntegerToDouble :: forall m a. Expr m a
mkIntegerToDouble = mkExpr (_S::S_ "IntegerToDouble") unit

_IntegerToDouble :: forall r. ExprPrism ( "IntegerToDouble" :: UNIT | r ) Unit
_IntegerToDouble = _ExprPrism (_S::S_ "IntegerToDouble")

mkDouble :: forall m a. Expr m a
mkDouble = mkExpr (_S::S_ "Double") unit

_Double :: forall r. ExprPrism ( "Double" :: UNIT | r ) Unit
_Double = _ExprPrism (_S::S_ "Double")

mkDoubleLit :: forall m a. Number -> Expr m a
mkDoubleLit = mkExpr (_S::S_ "DoubleLit")

_DoubleLit :: forall r. ExprPrism ( "DoubleLit" :: CONST Number | r ) Number
_DoubleLit = _ExprPrism (_S::S_ "DoubleLit")

mkDoubleShow :: forall m a. Expr m a
mkDoubleShow = mkExpr (_S::S_ "DoubleShow") unit

_DoubleShow :: forall r. ExprPrism ( "DoubleShow" :: UNIT | r ) Unit
_DoubleShow = _ExprPrism (_S::S_ "DoubleShow")

mkText :: forall m a. Expr m a
mkText = mkExpr (_S::S_ "Text") unit

_Text :: forall r. ExprPrism ( "Text" :: UNIT | r ) Unit
_Text = _ExprPrism (_S::S_ "Text")

mkTextLit :: forall m a. TextLitF (Expr m a) -> Expr m a
mkTextLit = mkExprF (_S::S_ "TextLit")

mkTextLit' :: forall m a. String -> Expr m a
mkTextLit' = mkTextLit <<< TextLit

_TextLit :: forall r. ExprFPrism ( "TextLit" :: FProxy TextLitF | r ) TextLitF
_TextLit = _ExprFPrism (_S::S_ "TextLit")

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
mkTextAppend = mkBinOp (_S::S_ "TextAppend")

_TextAppend :: forall r. BinOpPrism ( "TextAppend" :: FProxy Pair | r )
_TextAppend = _BinOpPrism (_S::S_ "TextAppend")

mkTextShow :: forall m a. Expr m a
mkTextShow = mkExpr (_S::S_ "TextShow") unit

_TextShow :: forall r. ExprPrism ( "TextShow" :: UNIT | r ) Unit
_TextShow = _ExprPrism (_S::S_ "TextShow")

mkList :: forall m a. Expr m a
mkList = mkExpr (_S::S_ "List") unit

_List :: forall r. ExprPrism ( "List" :: UNIT | r ) Unit
_List = _ExprPrism (_S::S_ "List")

mkListLit :: forall m a. Maybe (Expr m a) -> Array (Expr m a) -> Expr m a
mkListLit ty lit = mkExprF (_S::S_ "ListLit")
  (product ty lit)

_ListLit :: forall r o.
  Prism' (VariantF ( "ListLit" :: FProxy (Product Maybe Array) | r ) o)
  { ty :: Maybe o, values :: Array o }
_ListLit = _ExprFPrism (_S::S_ "ListLit") <<< _Newtype <<< iso into outof where
  into (Tuple ty values) = { ty, values }
  outof { ty, values } = Tuple ty values

mkListAppend :: forall m a. Expr m a -> Expr m a -> Expr m a
mkListAppend = mkBinOp (_S::S_ "ListAppend")

_ListAppend :: forall r. BinOpPrism ( "ListAppend" :: FProxy Pair | r )
_ListAppend = _BinOpPrism (_S::S_ "ListAppend")

mkListFold :: forall m a. Expr m a
mkListFold = mkExpr (_S::S_ "ListFold") unit

_ListFold :: forall r. ExprPrism ( "ListFold" :: UNIT | r ) Unit
_ListFold = _ExprPrism (_S::S_ "ListFold")

mkListBuild :: forall m a. Expr m a
mkListBuild = mkExpr (_S::S_ "ListBuild") unit

_ListBuild :: forall r. ExprPrism ( "ListBuild" :: UNIT | r ) Unit
_ListBuild = _ExprPrism (_S::S_ "ListBuild")

mkListLength :: forall m a. Expr m a
mkListLength = mkExpr (_S::S_ "ListLength") unit

_ListLength :: forall r. ExprPrism ( "ListLength" :: UNIT | r ) Unit
_ListLength = _ExprPrism (_S::S_ "ListLength")

mkListHead :: forall m a. Expr m a
mkListHead = mkExpr (_S::S_ "ListHead") unit

_ListHead :: forall r. ExprPrism ( "ListHead" :: UNIT | r ) Unit
_ListHead = _ExprPrism (_S::S_ "ListHead")

mkListLast :: forall m a. Expr m a
mkListLast = mkExpr (_S::S_ "ListLast") unit

_ListLast :: forall r. ExprPrism ( "ListLast" :: UNIT | r ) Unit
_ListLast = _ExprPrism (_S::S_ "ListLast")

mkListIndexed :: forall m a. Expr m a
mkListIndexed = mkExpr (_S::S_ "ListIndexed") unit

_ListIndexed :: forall r. ExprPrism ( "ListIndexed" :: UNIT | r ) Unit
_ListIndexed = _ExprPrism (_S::S_ "ListIndexed")

mkListReverse :: forall m a. Expr m a
mkListReverse = mkExpr (_S::S_ "ListReverse") unit

_ListReverse :: forall r. ExprPrism ( "ListReverse" :: UNIT | r ) Unit
_ListReverse = _ExprPrism (_S::S_ "ListReverse")

mkOptional :: forall m a. Expr m a
mkOptional = mkExpr (_S::S_ "Optional") unit

_Optional :: forall r. ExprPrism ( "Optional" :: UNIT | r ) Unit
_Optional = _ExprPrism (_S::S_ "Optional")

mkSome :: forall m a. Expr m a -> Expr m a
mkSome val = mkExprF (_S::S_ "Some")
  (Identity val)

_Some :: forall r o.
  Prism' (VariantF ( "Some" :: FProxy Identity | r ) o) o
_Some = _ExprFPrism (_S::S_ "Some") <<< _Newtype

mkNone :: forall m a. Expr m a
mkNone = mkExpr (_S::S_ "None") unit

_None :: forall r. ExprPrism ( "None" :: UNIT | r ) Unit
_None = _ExprPrism (_S::S_ "None")

mkOptionalFold :: forall m a. Expr m a
mkOptionalFold = mkExpr (_S::S_ "OptionalFold") unit

_OptionalFold :: forall r. ExprPrism ( "OptionalFold" :: UNIT | r ) Unit
_OptionalFold = _ExprPrism (_S::S_ "OptionalFold")

mkOptionalBuild :: forall m a. Expr m a
mkOptionalBuild = mkExpr (_S::S_ "OptionalBuild") unit

_OptionalBuild :: forall r. ExprPrism ( "OptionalBuild" :: UNIT | r ) Unit
_OptionalBuild = _ExprPrism (_S::S_ "OptionalBuild")

mkRecord :: forall m a. Functor m => m (Expr m a) -> Expr m a
mkRecord = mkExprF (_S::S_ "Record")

_Record :: forall r m. Functor m => ExprFPrism
  ( "Record" :: FProxy m | r ) m
_Record = _ExprFPrism (_S::S_ "Record")

_Record_empty :: forall r o m. MapLike String m =>
  Prism' (VariantF ( "Record" :: FProxy m | r ) o) Unit
_Record_empty = _Record <<< Dhall.Map._Empty

mkRecordLit :: forall a m. Functor m => m (Expr m a) -> Expr m a
mkRecordLit = mkExprF (_S::S_ "RecordLit")

_RecordLit :: forall r m. Functor m => ExprFPrism
  ( "RecordLit" :: FProxy m | r ) m
_RecordLit = _ExprFPrism (_S::S_ "RecordLit")

_RecordLit_empty :: forall r o m. MapLike String m =>
  Prism' (VariantF ( "RecordLit" :: FProxy m | r ) o) Unit
_RecordLit_empty = _RecordLit <<< Dhall.Map._Empty

mkUnion :: forall m a. Functor m => m (Maybe (Expr m a)) -> Expr m a
mkUnion = mkExprF (_S::S_ "Union") <<< Compose

_Union :: forall r m. Functor m => ExprFPrism ( "Union" :: FProxy (Compose m Maybe) | r ) (Compose m Maybe)
_Union = _ExprFPrism (_S::S_ "Union")

_Union_empty :: forall r o m. MapLike String m =>
  Prism' (VariantF ( "Union" :: FProxy (Compose m Maybe) | r ) o) Unit
_Union_empty = _Union <<< _Newtype <<< Dhall.Map._Empty

mkCombine :: forall m a. Expr m a -> Expr m a -> Expr m a
mkCombine = mkBinOp (_S::S_ "Combine")

_Combine :: forall r. BinOpPrism ( "Combine" :: FProxy Pair | r )
_Combine = _BinOpPrism (_S::S_ "Combine")

mkCombineTypes :: forall m a. Expr m a -> Expr m a -> Expr m a
mkCombineTypes = mkBinOp (_S::S_ "CombineTypes")

_CombineTypes :: forall r. BinOpPrism ( "CombineTypes" :: FProxy Pair | r )
_CombineTypes = _BinOpPrism (_S::S_ "CombineTypes")

mkPrefer :: forall m a. Expr m a -> Expr m a -> Expr m a
mkPrefer = mkBinOp (_S::S_ "Prefer")

_Prefer :: forall r. BinOpPrism ( "Prefer" :: FProxy Pair | r )
_Prefer = _BinOpPrism (_S::S_ "Prefer")

mkMerge :: forall m a. Expr m a -> Expr m a -> Maybe (Expr m a) -> Expr m a
mkMerge x y t = mkExprF (_S::S_ "Merge")
  (MergeF x y t)

_Merge :: forall r. ExprFPrism ( "Merge" :: FProxy MergeF | r ) MergeF
_Merge = _ExprFPrism (_S::S_ "Merge")

mkToMap :: forall m a. Expr m a -> Maybe (Expr m a) -> Expr m a
mkToMap x t = mkExprF (_S::S_ "ToMap")
  (Product (Tuple (Identity x) t))

_ToMap :: forall r. ExprFPrism ( "ToMap" :: FProxy (Product Identity Maybe) | r ) (Product Identity Maybe)
_ToMap = _ExprFPrism (_S::S_ "ToMap")

mkField :: forall m a. Expr m a -> String -> Expr m a
mkField expr field = mkExprF (_S::S_ "Field")
  (Tuple field expr)

_Field :: forall r o. Prism'
  (VariantF ( "Field" :: FProxy (Tuple String) | r ) o)
  (Tuple o String)
_Field = _ExprFPrism (_S::S_ "Field") <<< iso swap swap

mkProject :: forall m a. Expr m a -> Either (m Unit) (Expr m a) -> Expr m a
mkProject expr fields = mkExprF (_S::S_ "Project")
  (Product (Tuple (pure expr) (bimap App identity fields)))

_Project :: forall m r o. Prism'
  (VariantF ( "Project" :: FProxy (Product Identity (Either (App m Unit))) | r ) o)
  (Tuple o (Either (m Unit) o))
_Project = _ExprFPrism (_S::S_ "Project") <<< iso
  do \(Product (Tuple (Identity o) e)) -> Tuple o (bimap unwrap identity e)
  do \(Tuple o e) -> Product (Tuple (Identity o) (bimap App identity e))

mkAssert :: forall m a. Expr m a -> Expr m a
mkAssert = mkExprF (_S::S_ "Assert") <<< Identity

_Assert :: forall r o.
  Prism' (VariantF ( "Assert" :: FProxy Identity | r ) o) o
_Assert = _ExprFPrism (_S::S_ "Assert") <<< _Newtype

mkEquivalent :: forall m a. Expr m a -> Expr m a -> Expr m a
mkEquivalent = mkBinOp (_S::S_ "Equivalent")

_Equivalent :: forall r. BinOpPrism ( "Equivalent" :: FProxy Pair | r )
_Equivalent = _BinOpPrism (_S::S_ "Equivalent")

mkImportAlt :: forall m a. Expr m a -> Expr m a -> Expr m a
mkImportAlt = mkBinOp (_S::S_ "ImportAlt")

_ImportAlt :: forall r. BinOpPrism ( "ImportAlt" :: FProxy Pair | r )
_ImportAlt = _BinOpPrism (_S::S_ "ImportAlt")

mkUsingHeaders :: forall m a. Expr m a -> Expr m a -> Expr m a
mkUsingHeaders = mkBinOp (_S::S_ "UsingHeaders")

_UsingHeaders :: forall r. BinOpPrism ( "UsingHeaders" :: FProxy Pair | r )
_UsingHeaders = _BinOpPrism (_S::S_ "UsingHeaders")

mkHashed :: forall m a. Expr m a -> String -> Expr m a
mkHashed e hash = mkExprF (_S::S_ "Hashed") (Tuple hash e)

_Hashed :: forall r. ExprFPrism ( "Hashed" :: FProxy (Tuple String) | r ) (Tuple String)
_Hashed = _ExprFPrism (_S::S_ "Hashed")

mkEmbed :: forall m a. a -> Expr m a
mkEmbed = pure

_Embed :: forall a r. ExprPrism ( "Embed" :: CONST a | r ) a
_Embed = _ExprPrism (_S::S_ "Embed")

module Dhall.Core.AST.Operations.Location where

import Prelude

import Data.List (List, (:))
import Data.Maybe (Maybe)
import Data.Symbol (class IsSymbol, SProxy)
import Data.Tuple (Tuple(..))
import Data.Variant (Variant)
import Data.Variant as Variant
import Dhall.Core.AST (Expr, ExprRowVFI, Var)
import Prim.Row as Row
import Type.Row (type (+))

type Within r =
  ( "within" :: ExprRowVFI
  | r
  )
type Derived r =
  ( "typecheck" :: {}
  , "normalize" :: {}
  | r
  )
type Operated r =
  -- TODO: select specific variables to be substituted (`Set Var`?)
  ( "substitute" :: {}
  , "shift" :: { delta :: Int, variable :: Var }
  | r
  )

type LV r = List (Variant r)
type Pointer = LV (Within + ())
type Location = LV (Derived + Within + ())
type Derivation = LV (Operated + Derived + Within + ())
type TLV r = Tuple (LV r)
type PointerF = Tuple Pointer
type LocationF = Tuple Location
type DerivationF = Tuple Derivation
type BasedExprLocation m a = LocationF (Maybe (Expr m a))
type ExprLocation m a = LocationF (Expr m a)
type BasedExprDerivation m a = DerivationF (Maybe (Expr m a))
type ExprDerivation m a = DerivationF (Expr m a)

move ::
  forall sym ix all most.
    IsSymbol sym =>
    Row.Cons sym ix most all =>
  SProxy sym -> ix -> TLV all ~> TLV all
move sym ix (Tuple path base) = Tuple (Variant.inj sym ix : path) base

step ::
  forall sym all most.
    IsSymbol sym =>
    Row.Cons sym {} most all =>
  SProxy sym -> TLV all ~> TLV all
step sym = move sym mempty

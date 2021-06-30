module Dhall.Core.AST.Operations.Location where

import Prelude

import Control.Plus (empty)
import Data.Bifunctor (lmap)
import Data.List (List, (:))
import Data.Maybe (Maybe)
import Data.Symbol (class IsSymbol)
import Data.Traversable (traverse)
import Data.Tuple (Tuple)
import Data.Variant (Variant)
import Data.Variant as Variant
import Dhall.Core.AST (Expr, ExprRowVFI, Var, S_, _S)
import Prim.Row as Row
import Type.Proxy (Proxy)

type Within r =
  ( "within" :: ExprRowVFI
  | r
  )
type Derived r =
  ( "typecheck" :: {}
  , "normalize" :: {}
  , "alphaNormalize" :: {}
  | r
  )
type Operated r =
  -- TODO: select specific variables to be substituted (`Set Var`?)
  ( "substitute" :: {}
  , "shift" :: { delta :: Int, variable :: Var }
  | r
  )

type LV r = List (Variant r)
type Pointer = LV (Within ())
type Location = LV (Derived (Within ()))
type Derivation = LV (Operated (Derived (Within ())))
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
  Proxy sym -> ix -> LV all -> LV all
move sym ix path = Variant.inj sym ix : path

moveF ::
  forall sym ix all most.
    IsSymbol sym =>
    Row.Cons sym ix most all =>
  Proxy sym -> ix -> TLV all ~> TLV all
moveF sym ix = lmap (move sym ix)

stepF ::
  forall sym all most.
    IsSymbol sym =>
    Row.Cons sym {} most all =>
  Proxy sym -> TLV all ~> TLV all
stepF sym = moveF sym mempty

step ::
  forall sym all most.
    IsSymbol sym =>
    Row.Cons sym {} most all =>
  Proxy sym -> LV all -> LV all
step sym = move sym mempty

allWithin :: forall most. LV (Within most) -> Maybe (List ExprRowVFI)
allWithin = traverse $ Variant.on (_S::S_ "within") pure (pure empty)

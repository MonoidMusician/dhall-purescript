module Dhall.Interactive.Halogen where

import Prelude

import Data.Const (Const(..))
import Data.Functor.Variant (FProxy, SProxy(..), VariantF)
import Data.Functor.Variant as VariantF
import Data.Newtype (un, unwrap, wrap)
import Data.Newtype as N
import Data.Profunctor (dimap)
import Data.Profunctor.Star (Star(..))
import Data.Profunctor.Strong (first, second)
import Data.Symbol (class IsSymbol)
import Data.Tuple (Tuple(..))
import Dhall.Core.AST (BuiltinBinOps, Literals, Pair(..))
import Dhall.Interactive.Halogen.Types (RenderValue, RenderVariantF', RenderVariantF, boolH, doubleH, intH, naturalH, simpleC)
import Effect (Effect)
import Halogen.Aff as HA
import Halogen.HTML as HH
import Halogen.VDom.Driver (runUI)
import Data.Functor.Mu (Mu(..))
import Prim.Row as Row
import Type.Row (type (+))

renderCase :: forall g l l' b f k r r' a.
  Row.Cons k (FProxy f) r' r =>
  IsSymbol k =>
  Functor g =>
  Row.Cons k (FProxy f) l' l =>
  Functor f =>
  SProxy k ->
  (f a -> g (f b)) ->
  (VariantF r' a -> g (VariantF l b)) ->
  VariantF r a -> g (VariantF l b)
renderCase k f = VariantF.on k (f >>> map (VariantF.inj k))

literals :: forall ir or a.
  RenderVariantF' ir (Literals + or) a ->
  RenderVariantF' (Literals + ir) (Literals + or) a
literals rest = Star $ unwrap rest
  # renderCase (SProxy :: SProxy "BoolLit") (N.traverse Const (unwrap boolH))
  # renderCase (SProxy :: SProxy "NaturalLit") (N.traverse Const (unwrap naturalH))
  # renderCase (SProxy :: SProxy "IntegerLit") (N.traverse Const (unwrap intH))
  # renderCase (SProxy :: SProxy "DoubleLit") (N.traverse Const (unwrap doubleH))

both :: forall a or.
  RenderValue a ->
  RenderVariantF' (BuiltinBinOps + Literals + ()) (BuiltinBinOps + Literals + or) a
both param = builtinBinOps (literals (Star $ VariantF.case_)) param

rec :: forall r.
  (forall a. RenderValue a -> RenderVariantF r a) ->
  RenderValue (Mu (VariantF r))
rec f = Star \(In v) -> map In (un Star (f (rec f)) v)

builtinBinOps :: forall ir or a.
  RenderVariantF' ir (BuiltinBinOps + or) a ->
  RenderValue a -> RenderVariantF' (BuiltinBinOps + ir) (BuiltinBinOps + or) a
builtinBinOps rest param = Star
  let
    deal :: RenderValue (Tuple a a) -> RenderValue (Pair a)
    deal = dimap (\(Pair l r) -> Tuple l r) (\(Tuple l r) -> Pair l r)
    paramPair :: Pair a -> Pair (HH.HTML Void (Pair a))
    paramPair p = Pair (un Star (deal (first param)) p) (un Star (deal (second param)) p)
    renderBinOp s p =
      let Pair l r = paramPair p in
      HH.span_ [ l, HH.text (" " <> s <> " "), r ]
  in unwrap rest
  # renderCase (SProxy :: SProxy "BoolAnd") (renderBinOp "&&")
  # renderCase (SProxy :: SProxy "BoolOr") (renderBinOp "||")
  # renderCase (SProxy :: SProxy "BoolEQ") (renderBinOp "==")
  # renderCase (SProxy :: SProxy "BoolNE") (renderBinOp "!=")
  # renderCase (SProxy :: SProxy "NaturalPlus") (renderBinOp "+")
  # renderCase (SProxy :: SProxy "NaturalTimes") (renderBinOp "*")
  # renderCase (SProxy :: SProxy "TextAppend") (renderBinOp "++")
  # renderCase (SProxy :: SProxy "ListAppend") (renderBinOp "#")
  # renderCase (SProxy :: SProxy "Combine") (renderBinOp "∧")
  # renderCase (SProxy :: SProxy "CombineTypes") (renderBinOp "⩓")
  # renderCase (SProxy :: SProxy "Prefer") (renderBinOp "⫽")
  # renderCase (SProxy :: SProxy "ImportAlt") (renderBinOp "?")

main :: Effect Unit
main = HA.runHalogenAff do
  body <- HA.awaitBody
  let
    expr = In $ VariantF.inj (SProxy :: SProxy "CombineTypes") $ Pair
      (In $ VariantF.inj (SProxy :: SProxy "IntegerLit") $ wrap 0)
      (In $ VariantF.inj (SProxy :: SProxy "BoolLit") $ wrap true)
  driver <- runUI (simpleC (rec both)) expr body
  pure unit

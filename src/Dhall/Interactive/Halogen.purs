module Dhall.Interactive.Halogen where

import Prelude

import Data.Const (Const(..))
import Data.Functor.Mu (Mu(..))
import Data.Functor.Variant (FProxy, SProxy, VariantF)
import Data.Functor.Variant as VariantF
import Data.Newtype (un, unwrap, wrap)
import Data.Newtype as N
import Data.Profunctor (dimap)
import Data.Profunctor.Star (Star(..))
import Data.Profunctor.Strong (first, second)
import Data.Symbol (class IsSymbol)
import Data.Tuple (Tuple(..))
import Dhall.Core.AST (_S, S_, BuiltinBinOps, Literals, Pair(..))
import Dhall.Interactive.Halogen.Types (RenderValue, RenderVariantF', RenderVariantF, boolH, doubleH, intH, naturalH, simpleC)
import Effect (Effect)
import Halogen as H
import Halogen.Aff as HA
import Halogen.HTML as HH
import Halogen.VDom.Driver (runUI)
import Prim.Row as Row
import Type.Row (type (+))
import Data.Coyoneda (unCoyoneda)

silence :: forall h f i o m.
  H.Component h f i o m -> H.Component h (Const Void) i o m
silence = H.unComponent \c -> H.mkComponent
  { initialState: c.initialState
  , render: c.render
  , eval: c.eval <<< case _ of
      H.Initialize a -> H.Initialize a
      H.Finalize a -> H.Finalize a
      H.Receive i a -> H.Receive i a
      H.Action act a -> H.Action act a
      H.Query cv _ -> cv # unCoyoneda \_ (Const void) -> absurd void
  }

renderCase :: forall g l l' b f f' k r r' a.
  Row.Cons k (FProxy f) r' r =>
  IsSymbol k =>
  Functor g =>
  Row.Cons k (FProxy f') l' l =>
  Functor f' =>
  SProxy k ->
  (f a -> g (f' b)) ->
  (VariantF r' a -> g (VariantF l b)) ->
  VariantF r a -> g (VariantF l b)
renderCase k f = VariantF.on k (f >>> map (VariantF.inj k))

literals :: forall ir or a m.
  RenderVariantF' ir (Literals m + or) a ->
  RenderVariantF' (Literals m + ir) (Literals m + or) a
literals rest = Star $ unwrap rest
  # renderCase (_S::S_ "BoolLit") (N.traverse Const (unwrap boolH))
  # renderCase (_S::S_ "NaturalLit") (N.traverse Const (unwrap naturalH))
  # renderCase (_S::S_ "IntegerLit") (N.traverse Const (unwrap intH))
  # renderCase (_S::S_ "DoubleLit") (N.traverse Const (unwrap doubleH))

both :: forall a or m.
  RenderValue a ->
  RenderVariantF' (BuiltinBinOps m + Literals m + ()) (BuiltinBinOps m + Literals m + or) a
both param = builtinBinOps (literals (Star $ VariantF.case_)) param

rec :: forall r.
  (forall a. RenderValue a -> RenderVariantF r a) ->
  RenderValue (Mu (VariantF r))
rec f = Star \(In v) -> map In (un Star (f (rec f)) v)

builtinBinOps :: forall ir or a m.
  RenderVariantF' ir (BuiltinBinOps m + or) a ->
  RenderValue a -> RenderVariantF' (BuiltinBinOps m + ir) (BuiltinBinOps m + or) a
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
  # renderCase (_S::S_ "BoolAnd") (renderBinOp "&&")
  # renderCase (_S::S_ "BoolOr") (renderBinOp "||")
  # renderCase (_S::S_ "BoolEQ") (renderBinOp "==")
  # renderCase (_S::S_ "BoolNE") (renderBinOp "!=")
  # renderCase (_S::S_ "NaturalPlus") (renderBinOp "+")
  # renderCase (_S::S_ "NaturalTimes") (renderBinOp "*")
  # renderCase (_S::S_ "TextAppend") (renderBinOp "++")
  # renderCase (_S::S_ "ListAppend") (renderBinOp "#")
  # renderCase (_S::S_ "Combine") (renderBinOp "∧")
  # renderCase (_S::S_ "CombineTypes") (renderBinOp "⩓")
  # renderCase (_S::S_ "Prefer") (renderBinOp "⫽")
  # renderCase (_S::S_ "Equivalent") (renderBinOp "≡")

main :: Effect Unit
main = HA.runHalogenAff do
  body <- HA.awaitBody
  let
    expr = In $ VariantF.inj (_S::S_ "CombineTypes") $ Pair
      (In $ VariantF.inj (_S::S_ "IntegerLit") $ wrap 0)
      (In $ VariantF.inj (_S::S_ "BoolLit") $ wrap true)
  driver <- runUI (simpleC (rec both)) expr body
  pure unit

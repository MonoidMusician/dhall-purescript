module Dhall.Interactive.Halogen.Types where

import Prelude

import Data.Bifunctor (bimap)
import Data.Functor.Variant (FProxy, SProxy, VariantF)
import Data.Functor.Variant as VariantF
import Data.Int (fromString) as Int
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Number (fromString) as Number
import Data.Ord (abs, signum)
import Data.Profunctor.Star (Star(..))
import Data.Profunctor.Strong (first, second)
import Data.Symbol (class IsSymbol)
import Data.Tuple (Tuple(..))
import Dhall.Core.AST (Pair(..))
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties (InputType(..), StepValue(..))
import Halogen.HTML.Properties as HP
import Prim.Row as Row
import Unsafe.Coerce (unsafeCoerce)

type RenderValue v = RenderValue' v v
type RenderValue' = Star (HH.HTML Void)
type RenderVariantF r a = RenderVariantF' r r a
type RenderVariantF' ir or a = RenderValue' (VariantF ir a) (VariantF or a)

renderCase :: forall a or. RenderValue a -> RenderVariantF' () or a
renderCase _ = Star VariantF.case_

renderOn ::
  forall s f ir or ir' or' a.
    IsSymbol s =>
    Functor f =>
    Row.Cons s (FProxy f) ir' ir =>
    Row.Cons s (FProxy f) or' or =>
  SProxy s ->
  (RenderValue a -> RenderValue (f a)) ->
  (RenderValue a -> RenderVariantF' ir' or' a) ->
  (RenderValue a -> RenderVariantF' ir or a)
renderOn s h r a = Star $ VariantF.on s
  (unwrap $ map (VariantF.inj s) $ h a)
  (unwrap $ map unsafeCoerce $ r a)

renderProd :: forall a b.
  RenderValue a ->
  RenderValue b ->
  Tuple a b ->
  Tuple (HH.HTML Void (Tuple a b)) (HH.HTML Void (Tuple a b))
renderProd a b t = Tuple
  (unwrap (first a) t)
  (unwrap (second b) t)

renderPair :: forall a.
  RenderValue a ->
  Pair a ->
  Pair (HH.HTML Void (Pair a))
renderPair a (Pair l r) =
  let Tuple l' r' = renderProd a a (Tuple l r) in
  Pair l' r' <#> map \(Tuple l'' r'') -> Pair l'' r''

naturalH :: RenderValue Int
naturalH = Star \v -> HH.input
  [ HP.type_ InputNumber
  , HP.min 0.0
  , HP.step (Step 1.0)
  , HP.value (show (abs v))
  , HE.onValueInput (Int.fromString >>> map abs)
  ]

boolH :: RenderValue Boolean
boolH = Star \v ->
  HH.button [ HE.onClick (pure (pure (not v))) ]
    [ HH.text if v then "True" else "False" ]

intH :: RenderValue Int
intH = Star \v -> HH.span_
  [ HH.button [ HE.onClick (pure (pure (negate v))) ]
    [ HH.text if v < 0 then "-" else "+" ]
  , unwrap naturalH v <#> mul (signum v)
  ]

stringH :: RenderValue String
stringH = Star \v -> HH.input
  [ HP.type_ InputText
  , HP.value v
  , HE.onValueInput pure
  ]

doubleH :: RenderValue Number
doubleH = Star \v -> HH.input
  [ HP.type_ InputNumber
  , HP.step (Step 0.5)
  , HP.value (show (abs v))
  , HE.onValueInput Number.fromString
  ]

data InOut v a = In a v | Out a v

simpleC :: forall v m.
  RenderValue v ->
  H.Component HH.HTML (InOut v) v v m
simpleC renderer = H.component
  { initializer: Nothing
  , finalizer: Nothing
  , receiver: Just <<< In unit
  , initialState: identity
  , eval: case _ of
      In a v -> a <$ H.put v
      Out a v -> a <$ H.put v <* H.raise v
  , render: bimap absurd (Out unit) <<< unwrap renderer
  }

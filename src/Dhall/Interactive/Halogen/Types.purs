module Dhall.Interactive.Halogen.Types where

import Prelude

import Data.Bifunctor (bimap)
import Data.Functor.Variant (VariantF)
import Data.Int (fromString) as Int
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Number (fromString) as Number
import Data.Ord (abs, signum)
import Data.Profunctor.Star (Star(..))
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties (InputType(..), StepValue(..))
import Halogen.HTML.Properties as HP

type RenderValue v = RenderValue' v v
type RenderValue' = Star (HH.HTML Void)
type RenderVariantF r a = RenderVariantF' r r a
type RenderVariantF' ir or a = RenderValue' (VariantF ir a) (VariantF or a)

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

module Dhall.Interactive.Halogen.Icons where

import Prelude

import Data.Profunctor.Star (Star(..))
import Data.Tuple (Tuple(..))
import Dhall.Interactive.Halogen.Types (simpleC)
import Effect (Effect)
import Halogen (AttrName(..), ClassName(..), ElemName(..), Namespace(..))
import Halogen as H
import Halogen.Aff as HA
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties (InputType(..))
import Halogen.HTML.Properties as HP
import Halogen.VDom.Driver (runUI)
import Web.UIEvent.KeyboardEvent (KeyboardEvent)
import Web.UIEvent.MouseEvent (MouseEvent)
import Web.UIEvent.WheelEvent (WheelEvent)

svgNS = Namespace "http://www.w3.org/2000/svg" :: Namespace
xlinkNS = Namespace "http://www.w3.org/1999/xlink" :: Namespace

type CoreAttributes r = (id :: String | r)

type StyleAttributes r = ("class" :: String | r)

-- Subset of events that work on Firefox 60/Chromium 66
type GlobalEventAttributes r =
  ( onClick :: MouseEvent
  , onDoubleClick :: MouseEvent
  , onContextMenu :: MouseEvent
  , onKeyDown :: KeyboardEvent
  , onKeyPress :: KeyboardEvent
  , onKeyUp :: KeyboardEvent
  , onMouseDown :: MouseEvent
  , onMouseEnter :: MouseEvent
  , onMouseLeave :: MouseEvent
  , onMouseMove :: MouseEvent
  , onMouseOut :: MouseEvent
  , onMouseOver :: MouseEvent
  , onMouseUp :: MouseEvent
  , onWheel :: WheelEvent
  | r)

-- These can also be done with CSS
type PresentationAttributes r = (stroke :: String, fill :: String | r)

type GlobalAttributes r = (PresentationAttributes (GlobalEventAttributes (StyleAttributes (CoreAttributes r))))

type SVGsvg = GlobalAttributes
  ( width :: Number
  , height :: Number
  , viewBox :: String
  , preserveAspectRatio :: String
  )

type SVGcircle = GlobalAttributes
  ( cx :: Number
  , cy :: Number
  , r :: Number
  , transform :: String
  )

type SVGellipse = GlobalAttributes
  ( cx :: Number
  , cy :: Number
  , rx :: Number
  , ry :: Number
  , transform :: String
  )

type SVGrect = GlobalAttributes
  ( x :: Number
  , y :: Number
  , rx :: Number
  , ry :: Number
  , width :: Number
  , height :: Number
  , transform :: String
  )

type SVGg = GlobalAttributes
  ( transform :: String )

type SVGpath = GlobalAttributes
  ( d :: String
  , transform :: String
  )

type SVGline = GlobalAttributes
  ( x1 :: Number
  , y1 :: Number
  , x2 :: Number
  , y2 :: Number
  , transform :: String
  )

type SVGtext = GlobalAttributes
  ( x :: Number
  , y :: Number
  , text_anchor :: String
  , dominant_baseline :: String
  , transform :: String
  )

type SVGforeignObject = GlobalAttributes
  ( x :: Number
  , y :: Number
  , height :: Number
  , width :: Number
  )

type SVGuse = GlobalAttributes
  ( x :: Number
  , y :: Number
  , height :: Number
  , width :: Number
  , href :: String
  )


svg :: forall p i. HH.Node SVGsvg p i
svg = HH.elementNS svgNS (ElemName "svg")
use :: forall p i. HH.Leaf SVGuse p i
use = HH.elementNS svgNS (ElemName "use") <@> []

class_ :: forall r i. String -> HH.IProp ( class :: String | r ) i
class_ = HP.attr (AttrName "class")

href :: forall r i. String -> HH.IProp ( href :: String | r ) i
href = HP.attr (AttrName "href")

icon :: forall p i. String -> HH.Leaf SVGsvg p i
icon i = svg <@> [ use [ href $ "feather-sprite.svg#" <> i ]]

main :: Effect Unit
main = HA.runHalogenAff do
  body <- HA.awaitBody
  let
    icon_top = Tuple "icon-top"
    move = icon "menu" [ class_ "feather active move vertical" ]
    remove = icon "minus-square" [ class_ "feather active" ]
    row items = HH.div [ HP.class_ $ ClassName "row" ] $ HH.div_ <<< pure <$> items
    labelled label value = row
      [ HH.input
        [ HP.type_ InputText
        , HP.class_ $ ClassName "id-input"
        , HP.value label
        ]
      , HH.text ":"
      , value
      ]
    record_start k v =
      [ icon_top $ icon "minimize" [ class_ "feather active" ]
      , pure $ HH.text "{"
      , icon_top move
      , pure $ labelled k v
      , icon_top remove
      ]
    record_continue k v =
      [ pure $ HH.text ""
      , pure $ HH.text ","
      , icon_top move
      , pure $ labelled k v
      , icon_top $ remove
      ]
    record_end =
      [ Tuple "icon-bottom" $ icon "minimize" [ class_ "feather active" ]
      , pure $ HH.text "}"
      , Tuple "icon-bottom" $ icon "plus-square" [ class_ "feather active" ]
      ]
    c = Star \_ -> HH.div [ HP.class_ $ ClassName "grid-container" ] $
      join $ map (\(Tuple cls v) -> HH.div [ HP.class_ $ ClassName cls ] [ v ]) <$>
        [ record_start "id" $ HH.text "2014"
        , record_continue "name" $ HH.text "“Lydia”"
        , record_end
        ]
  driver <- runUI (simpleC c) unit body
  pure unit

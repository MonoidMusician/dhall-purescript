module Dhall.Interactive.Halogen.Icons where

import Prelude

import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Web.UIEvent.KeyboardEvent (KeyboardEvent)
import Web.UIEvent.MouseEvent (MouseEvent)
import Web.UIEvent.WheelEvent (WheelEvent)

svgNS = H.Namespace "http://www.w3.org/2000/svg" :: H.Namespace
xlinkNS = H.Namespace "http://www.w3.org/1999/xlink" :: H.Namespace

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
  | r
  )

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
svg = HH.elementNS svgNS (H.ElemName "svg")

use :: forall p i. HH.Leaf SVGuse p i
use = HH.elementNS svgNS (H.ElemName "use") <@> []

class_ :: forall r i. String -> HH.IProp ( class :: String | r ) i
class_ = HP.attr (H.AttrName "class")

href :: forall r i. String -> HH.IProp ( href :: String | r ) i
href = HP.attr (H.AttrName "href")

icon :: forall p i. String -> HH.Leaf SVGsvg p i
icon i = svg <@> [ use [ href $ "feather-sprite.svg#" <> i ]]

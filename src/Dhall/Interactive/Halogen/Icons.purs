module Dhall.Interactive.Halogen.Icons where

import Prelude

import Control.Bind (bindFlipped)
import Control.Monad.Free (Free)
import DOM.HTML.Indexed (HTMLbutton)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), isNothing)
import Data.Profunctor.Star (Star(..))
import Data.Symbol (SProxy(..))
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff, error, throwError)
import Effect.Class.Console (logShow)
import Halogen (AttrName(..), ClassName(..), ElemName(..), Namespace(..))
import Halogen as H
import Halogen.Aff as HA
import Halogen.Expanding as TCHE
import Halogen.HTML as HH
import Halogen.HTML.Elements.Keyed as HK
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties (InputType(..))
import Halogen.HTML.Properties as HP
import Halogen.VDom.Driver (runUI)
import Halogen.Zuruzuru as Zuruzuru
import Web.UIEvent.KeyboardEvent (KeyboardEvent)
import Web.UIEvent.MouseEvent (MouseEvent)
import Web.UIEvent.WheelEvent (WheelEvent)
import Web.Util.TextCursor as TC

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
svg = HH.elementNS svgNS (ElemName "svg")
use :: forall p i. HH.Leaf SVGuse p i
use = HH.elementNS svgNS (ElemName "use") <@> []

class_ :: forall r i. String -> HH.IProp ( class :: String | r ) i
class_ = HP.attr (AttrName "class")

href :: forall r i. String -> HH.IProp ( href :: String | r ) i
href = HP.attr (AttrName "href")

icon :: forall p i. String -> HH.Leaf SVGsvg p i
icon i = svg <@> [ use [ href $ "feather-sprite.svg#" <> i ]]

data Q a
  = ZZ (Zuruzuru.Message String) a
  | Swap a

settings :: TCHE.Settings
settings =
  { focused:
    { min: 100.0
    , max: 600.0
    , padding: 50.0
    }
  , blurred:
    { min: 100.0
    , max: 600.0
    , padding: 50.0
    }
  }

data QE a
  = Down String a
  | Up TCHE.Blurry a
  | PassOn (Free TCHE.Query a)

expanding :: H.Component HH.HTML QE String String Aff
expanding = H.component
  { initialState: TCHE.Blurred
  , initializer: Nothing
  , finalizer: Nothing
  , receiver: HE.input Down
  , eval: case _ of
      Down new next -> next <$ do
        old <- H.get
        when (new /= TCHE.toString old) do
          H.put (TCHE.Blurred new)
      Up new next -> next <$ do
        old <- H.get
        when (new /= old) do
          H.put new
          H.raise (TCHE.toString new)
      -- Let the caller query the expanding component directly
      -- But make sure we grab the new state so we are not surprised
      PassOn q -> H.query (SProxy :: SProxy "") unit (Tuple <$> q <*> TCHE.get) >>= case _ of
        Nothing -> throwError $ error "expanding component should have child"
        Just (Tuple a new) -> a <$ H.put new
  , render: \b ->
    HH.slot (SProxy :: SProxy "") unit TCHE.expandingComponent (Tuple settings b)
      (HE.input Up)
  }

type Slots =
  ( expanding :: H.Slot QE String Zuruzuru.Key
  )

interactive :: H.Component HH.HTML Q Unit Void Aff
interactive = H.component
  { initializer: Nothing
  , finalizer: Nothing
  , receiver: pure Nothing
  , initialState: pure { values: [], shown: true }
  , eval: case _ of
      ZZ (Zuruzuru.NewState v) a -> a <$ H.modify_ _ { values = v } <* logShow v
      ZZ (Zuruzuru.Added info) a -> a <$ do
        logShow info
        bindFlipped logShow $ H.query (SProxy :: SProxy "zuruzuru") unit $
          Zuruzuru.queryInside (SProxy :: SProxy "expanding") info.key $
            PassOn $ (TCHE.set (TCHE.Focused TC.empty) *> TCHE.get)
      ZZ _ a -> pure a
      Swap a -> a <$ H.modify_ \r -> r { shown = not r.shown }
  , render
  } where
    lifting (Left m) = Just (ZZ m unit)
    lifting (Right _) = Just (Swap unit)

    render ::
      { values :: Array String, shown :: Boolean } ->
      H.ComponentHTML
        Q
        ( zuruzuru :: Zuruzuru.Slot' Slots Aff Unit String Unit )
        Aff
    render { shown: false } =
      HH.div [ HP.class_ $ H.ClassName "ast" ]
        [ HH.text "{"
        , btn (Just (Swap unit)) "more-horizontal" "feather inline active"
        , HH.text "}"
        ]
    render { values: vs } = HH.slot Zuruzuru._zuruzuru unit Zuruzuru.zuruzuru' (com vs) lifting
    btn :: forall q ps. Maybe (q Unit) -> String -> String -> H.ComponentHTML q ps Aff
    btn q = btn' [ HE.onClick (pure q), HP.disabled (isNothing q) ]
    btn' :: forall q ps. Array (HH.IProp HTMLbutton (q Unit)) -> String -> String -> H.ComponentHTML q ps Aff
    btn' p t c = HH.button p [ icon t [ class_ c ] ]
    add_btn :: forall ps. String -> String -> Zuruzuru.RenderAdder ps Aff
    add_btn t c q = Just $ btn (Just q) t c

    com :: Array String -> Zuruzuru.Input' Slots Aff Unit String
    com vs =
      { values: vs
      , direction: Zuruzuru.Vertical
      , default: pure mempty
      , renderer
      }

    renderer = Zuruzuru.Renderer \datums { add, output } ->
      HH.div [ HP.class_ $ H.ClassName "ast" ] $ pure $
      let postpend = add (Array.length datums) in
      if Array.null datums
      then HH.span_
          [ HH.text "{"
          , btn (Just postpend) "plus-square" "feather inline active"
          , HH.text "}"
          ]
      else HK.div [ HP.class_ $ H.ClassName "grid-container" ]
        let
          items = datums <#> \{ helpers, handle, info } ->
            let
              moving :: forall r i. HP.IProp ( style :: String | r ) i
              moving = HP.attr (H.AttrName "style") $
                "transform: translateY(" <> show info.offset <> "px)"
            in Tuple info.key $ HH.div [ HP.class_ $ H.ClassName "row" ]
            [ if info.index == 0
              then btn (Just (output unit)) "minimize" "feather inline active"
              else HH.span_ $ pure $ icon "more-vertical" [ class_ "feather inline passive" ]
            , HH.div_ [ HH.text if info.index == 0 then "{" else "," ]
            , btn'
              [ moving
              , HP.ref handle.label
              , HE.onMouseDown handle.onMouseDown
              , HP.class_ (H.ClassName "move")
              , HP.tabIndex (-1)
              ] "menu" "feather inline active move vertical"
            , btn' [ moving, HE.onClick (\_ -> Just helpers.remove) ] "minus-square" "feather inline active"
            , HH.span [ HP.class_ (H.ClassName "input-parent"), moving ]
              [ HH.slot (SProxy :: SProxy "expanding") info.key
                  expanding info.value (Just <<< helpers.set)
              ]
            ]
        in items <>
          [ Tuple "" $ HH.div
            [ HP.class_ $ H.ClassName "row" ]
            [ btn (Just (output unit)) "minimize" "feather inline active"
            , HH.text "}"
            , btn (Just postpend) "plus-square" "feather inline active"
            ]
          ]

main :: Effect Unit
main = HA.runHalogenAff do
  body <- HA.awaitBody
  let
    icon_top = Tuple "icon-top"
    move = icon "menu" [ class_ "feather inline active move vertical" ]
    remove = icon "minus-square" [ class_ "feather inline active" ]
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
      [ icon_top $ icon "minimize" [ class_ "feather inline active" ]
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
      [ Tuple "icon-bottom" $ icon "minimize" [ class_ "feather inline active" ]
      , pure $ HH.text "}"
      , Tuple "icon-bottom" $ icon "plus-square" [ class_ "feather inline active" ]
      ]
    c = Star \_ -> HH.div [ HP.class_ $ ClassName "grid-container" ] $
      join $ map (\(Tuple cls v) -> HH.div [ HP.class_ $ ClassName cls ] [ v ]) <$>
        [ record_start "id" $ HH.text "2014"
        , record_continue "name" $ HH.text "“Lydia”"
        , record_end
        ]
  driver <- runUI interactive unit body
  pure unit

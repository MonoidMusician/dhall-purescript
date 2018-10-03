module Dhall.Interactive where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))
import Data.Tuple (Tuple(..))
import Dhall.Interactive.Halogen.Inputs as Inputs
import Effect (Effect)
import Effect.Aff (Aff)
import Halogen as H
import Halogen.Aff as HA
import Halogen.Expanding as TCHE
import Halogen.HTML as HH
import Halogen.HTML.Elements.Keyed as HK
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.VDom.Driver (runUI)
import Halogen.Zuruzuru as Zuruzuru
import Web.Util.TextCursor as TC

data Q a
  = ZZ (Zuruzuru.Message String) a
  | Swap a

type Slots =
  ( expanding :: H.Slot Inputs.QueryExpanding String Zuruzuru.Key
  )

interactive :: H.Component HH.HTML Q Unit Void Aff
interactive = H.component
  { initializer: Nothing
  , finalizer: Nothing
  , receiver: pure Nothing
  , initialState: pure { values: [], shown: true }
  , eval: case _ of
      ZZ (Zuruzuru.NewState v) a -> a <$ H.modify_ _ { values = v }
      ZZ (Zuruzuru.Added info) a -> a <$ do
        H.query (SProxy :: SProxy "zuruzuru") unit $
          Zuruzuru.queryInside (SProxy :: SProxy "expanding") info.key $
            Inputs.PassOn $ (TCHE.set (TCHE.Focused TC.empty) *> TCHE.get)
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
        , Inputs.inline_feather_button_action (Just (Swap unit)) "more-horizontal"
        , HH.text "}"
        ]
    render { values: vs } =
      HH.slot Zuruzuru._zuruzuru unit Zuruzuru.zuruzuru' (com vs) lifting

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
          , Inputs.inline_feather_button_action (Just postpend) "plus-square"
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
            [ Inputs.inline_feather_button_action (Just (output unit))
              if info.index == 0
              then "minimize"
              else "more-vertical"
            , HH.div_ [ HH.text if info.index == 0 then "{" else "," ]
            , Inputs.icon_button_props
              [ moving
              , HP.ref handle.label
              , HE.onMouseDown handle.onMouseDown
              , HP.class_ (H.ClassName "move")
              , HP.tabIndex (-1)
              ] "menu" "feather inline active move vertical"
            , Inputs.inline_feather_button_props [ moving, HE.onClick (\_ -> Just helpers.remove) ] "minus-square"
            , HH.span [ HP.class_ (H.ClassName "input-parent"), moving ]
              [ HH.slot (SProxy :: SProxy "expanding") info.key
                  Inputs.expanding info.value (Just <<< helpers.set)
              ]
            ]
        in items <>
          [ Tuple "" $ HH.div
            [ HP.class_ $ H.ClassName "row" ]
            [ Inputs.inline_feather_button_action (Just (output unit)) "minimize"
            , HH.text "}"
            , Inputs.inline_feather_button_action (Just postpend) "plus-square"
            ]
          ]

main :: Effect Unit
main = HA.runHalogenAff do
  body <- HA.awaitBody
  driver <- runUI interactive unit body
  pure unit

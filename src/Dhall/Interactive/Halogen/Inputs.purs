module Dhall.Interactive.Halogen.Inputs where

import Prelude

import CSS as CSS
import Control.Monad.Free (Free)
import DOM.HTML.Indexed (HTMLbutton)
import Data.Exists (mkExists)
import Data.Maybe (Maybe(..), isNothing)
import Data.Symbol (SProxy(..))
import Data.Tuple (Tuple(..))
import Dhall.Interactive.Halogen.Icons as Icons
import Effect.Aff (Aff, error, throwError)
import Halogen as H
import Halogen.Expanding as TCHE
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

data QueryExpanding a
  = Down String a
  | Up TCHE.Blurry a
  | PassOn (Free TCHE.Query a)

settings :: HP.InputType -> TCHE.Settings
settings t =
  { classes: []
  , type_: t
  , padding:
    { focused: mkExists $ 2.0 # CSS.em
    , blurred: mkExists $ 1.0 # CSS.em
    }
  , style: do
      CSS.minWidth $ 5.0 # CSS.em
      CSS.maxWidth $ 20.0 # CSS.em
      CSS.key (CSS.fromString "text-overflow") "ellipsis"
  }

expanding :: HP.InputType -> H.Component HH.HTML QueryExpanding String String Aff
expanding t = H.component
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
        Just (Tuple a new) -> a <$ do
          old <- H.get
          when (new /= old) do
            H.put new
  , render: \b ->
      HH.slot (SProxy :: SProxy "") unit TCHE.expandingComponent
        (Tuple (settings t) b) (HE.input Up)
  }

icon_button_action :: forall q ps.
  Maybe (q Unit) ->
  String ->
  String ->
  H.ComponentHTML q ps Aff
icon_button_action q = icon_button_props [ HE.onClick (pure q), HP.disabled (isNothing q) ]

icon_button_props :: forall q ps.
  Array (HH.IProp HTMLbutton (q Unit)) ->
  String ->
  String ->
  H.ComponentHTML q ps Aff
icon_button_props p t c = HH.button p [ Icons.icon t [ Icons.class_ c ] ]

inline_feather_button_action :: forall q ps.
  Maybe (q Unit) ->
  String ->
  H.ComponentHTML q ps Aff
inline_feather_button_action q t = icon_button_action q t "feather inline active"

inline_feather_button_props :: forall q ps.
  Array (HH.IProp HTMLbutton (q Unit)) ->
  String ->
  H.ComponentHTML q ps Aff
inline_feather_button_props p t = icon_button_props p t "feather inline active"

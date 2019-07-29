module Dhall.Interactive.Halogen.AST where

import Prelude

import Control.Comonad (extract)
import Control.Comonad.Cofree (Cofree)
import Control.Comonad.Env (EnvT(..))
import Data.Array as Array
import Data.Bifunctor (bimap, lmap)
import Data.Const (Const)
import Data.Either (Either(..), either)
import Data.Functor.Compose (Compose)
import Data.Functor.Variant (VariantF)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, un)
import Data.Profunctor (dimap)
import Data.Profunctor.Star (Star(..))
import Data.Symbol (SProxy(..))
import Data.Tuple (Tuple(..), fst)
import Dhall.Core.AST as AST
import Dhall.Map as Dhall.Map
import Dhall.Interactive.Halogen.Inputs (QueryExpanding)
import Dhall.Interactive.Halogen.Inputs as Inputs
import Dhall.Interactive.Halogen.Types (RenderValue_)
import Effect.Aff (Aff)
import Halogen as H
import Halogen.Component as HC
import Halogen.Component.Profunctor (ProComponent(..))
import Halogen.HTML as HH
import Halogen.HTML.Elements.Keyed as HK
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.VDom.Thunk as Thunk
import Halogen.Zuruzuru as Zuruzuru
import Type.Row (type (+))

type Slot = Array String

newtype SlottedHTML r o = SlottedHTML (H.ComponentHTML o r Aff)
instance functorSlottedHTML :: Functor (SlottedHTML a) where
  map f (SlottedHTML h) =  SlottedHTML $ bimap mapSlot f h where
    mapSlot (HC.ComponentSlot s) = HC.ComponentSlot $ map f s
    mapSlot (HC.ThunkSlot s) = HC.ThunkSlot $ Thunk.hoist (lmap mapSlot) $ map f s
derive instance newtypeSlottedHTML :: Newtype (SlottedHTML a o) _

expanding :: forall o r. Slot -> String -> (String -> o) ->
  SlottedHTML (Expandable r) o
expanding slot value inj = SlottedHTML $
  HH.slot (SProxy :: SProxy "expanding") (slot <> ["label"])
    (Inputs.expanding HP.InputText) value
    (Just <<< inj)

overEnvT :: forall h annot a f g i. Functor h =>
  (i -> Star h (f a) (g a)) ->
  (i -> Star h (EnvT annot f a) (EnvT annot g a))
overEnvT f i = Star \(EnvT (Tuple annot f'a)) ->
  un Star (f i) f'a <#> \g'a -> EnvT (Tuple annot g'a)

type Renderer r e o = Zuruzuru.Renderer r Aff o e
type State r e o =
  { default :: e
  , renderer :: Renderer r e o
  , values :: Array e
  }
type Input r e o = Tuple
  { default :: e
  , renderer :: Renderer r e o
  }
  (Array e)

listicle :: forall r e o.
  H.Component HH.HTML (Const Void) (Input r e o) (Either o (Array e)) Aff
listicle = H.mkComponent
  { initialState: toState
  , render
  , eval: case _ of
      (H.Initialize a) -> pure a
      (H.Finalize a) -> pure a
      (H.Receive i a) -> a <$ H.put (toState i)
      (H.Query _ a) -> pure (a unit)
      (H.Action (Left o) a) -> a <$ H.raise (Left o)
      (H.Action (Right message) a) -> case message of
        Zuruzuru.NewState v -> a <$
          H.modify_ _ { values = v } <* H.raise (Right v)
        {-
        Zuruzuru.Added info -> a <$
          H.query (SProxy :: SProxy "zuruzuru") unit do
            Zuruzuru.queryInside (SProxy :: SProxy "expanding") [info.key] $
              Inputs.PassOn $ (TCHE.set (TCHE.Focused TC.empty) *> TCHE.get)
        -}
        _ -> pure a
  } where
    toState :: Input r e o -> State r e o
    toState (Tuple { default, renderer } values) =
      { default, renderer, values }

    render :: State r e o ->
      H.ComponentHTML (Either o (Zuruzuru.Message e))
        ( zuruzuru :: Zuruzuru.Slot'
          r
          Aff o e Unit
        )
        Aff
    render st =
      HH.slot Zuruzuru._zuruzuru unit Zuruzuru.zuruzuru' (com st) lifting

    lifting (Left m) = Just (Right m)
    lifting (Right o) = Just (Left o)

    com :: State r e o -> Zuruzuru.Input' r Aff o e
    com st =
      { values: st.values
      , direction: Zuruzuru.Vertical
      , default: pure st.default
      , renderer: st.renderer
      }

type InputIOSM r e o = Tuple
  { default :: e
  , renderer :: Renderer r (Tuple String e) o
  }
  (Dhall.Map.InsOrdStrMap e)

listicleIOSM :: forall r e o.
  H.Component HH.HTML (Const Void) (InputIOSM r e o) (Either o (Dhall.Map.InsOrdStrMap e)) Aff
listicleIOSM = un ProComponent $ ProComponent listicle # dimap
  do bimap (\i -> i { default = Tuple mempty i.default }) Dhall.Map.unIOSM
  do map Dhall.Map.mkIOSM

type Expandable r =
  ( expanding :: H.Slot QueryExpanding String (Array String)
  | r
  )
type ExpandableHTML r a = H.ComponentHTML a (Expandable r) Aff

mkIOSMRenderer :: forall e r o.
  Array (Array (SlottedHTML (Expandable r) o)) ->
  (Int -> String) ->
  String ->
  String ->
  (Zuruzuru.Key -> e -> SlottedHTML (Expandable r) e) ->
  Zuruzuru.Renderer (Expandable r) Aff (Either Unit o) (Tuple String e)
mkIOSMRenderer prior syntax sep close each = Zuruzuru.Renderer \datums { add, output } ->
  HH.div [ HP.class_ $ H.ClassName "ast" ] $ pure $
  let postpend = add (Array.length datums) in
  if Array.null datums
  then HH.span_
      [ HH.text $ syntax (-1)
      , Inputs.inline_feather_button_action (Just postpend) "plus-square" "Add field"
      , HH.text close
      ]
  else HK.div [ HP.class_ $ H.ClassName "grid-container" ]
    let
      items = datums <#> \r ->
        renderIOSMItems (SlottedHTML <<< HH.text <<< syntax) (SlottedHTML $ HH.text $ sep) each (output <<< Left)
          (r { helpers { output = r.helpers.output <<< Left } })
      before = prior # mapWithIndex \i e ->
        Tuple ("before-"<>show i) $
          HH.div
          [ HP.class_ $ H.ClassName "row" ] $
            un SlottedHTML <<< map (output <<< Right) <$> e
    in before <> items <>
      [ Tuple "last" $ HH.div
        [ HP.class_ $ H.ClassName "row" ]
        [ Inputs.inline_feather_button_action (Just (output (Left unit))) "minimize" "Collapse"
        , HH.text close
        , Inputs.inline_feather_button_action (Just postpend) "plus-square" "Add field"
        ]
      ]

renderIOSMItems :: forall e r q.
  (Int -> SlottedHTML (Expandable r) Void) ->
  SlottedHTML (Expandable r) Void ->
  (Zuruzuru.Key -> e -> SlottedHTML (Expandable r) e) ->
  (Unit -> q) ->
  { helpers :: Zuruzuru.Helpers Unit q (Tuple String e)
  , handle :: Zuruzuru.Handle' q
  , info :: Zuruzuru.ItemInfo' (Tuple String e)
  } -> Tuple String (ExpandableHTML r q)
renderIOSMItems syntax sep each output { helpers, handle, info } =
  let
    moving :: forall p i. HP.IProp ( style :: String | p ) i
    moving = HP.attr (H.AttrName "style") $
      "transform: translateY(" <> show info.offset <> "px)"
  in Tuple ("item-"<>info.key) $ HH.div [ HP.class_ $ H.ClassName "row" ]
  [ Inputs.inline_feather_button_action (Just (output unit))
    (if info.index == 0
    then "minimize"
    else "more-vertical")
    "Collapse"
  , HH.div_ [ un SlottedHTML $ absurd <$> syntax info.index ]
  , Inputs.icon_button_props
    [ moving
    , HP.ref handle.label
    , HE.onMouseDown handle.onMouseDown
    , HP.class_ (H.ClassName "move")
    , HP.tabIndex (-1)
    , HP.attr (H.AttrName "data-tooltip") "Reorder (drag/drop)"
    ] "menu" "feather inline active move vertical"
  , Inputs.inline_feather_button_props [ moving, HE.onClick (\_ -> Just helpers.remove), HP.attr (H.AttrName "data-tooltip") "Remove field" ] "minus-square"
  , HH.span [ HP.class_ (H.ClassName "input-parent"), moving ]
    [ HH.slot (SProxy :: SProxy "expanding") [info.key]
        (Inputs.expanding HP.InputText) (fst info.value)
        (Just <<< (Tuple <@> extract info.value) >>> helpers.set)
    , un SlottedHTML $ absurd <$> sep
    , un SlottedHTML $ each info.key (extract info.value) <#>
        (Tuple (fst info.value) >>> helpers.set)
    ]
  ]

mkArrayRenderer :: forall e r o.
  { before :: Array (Array (SlottedHTML (Expandable r) (Either Unit o)))
  , after  :: Array (Array (SlottedHTML (Expandable r) (Either Unit (Either Unit o))))
  } ->
  (Int -> String) ->
  (Zuruzuru.Key -> e -> SlottedHTML (Expandable r) e) ->
  Zuruzuru.Renderer (Expandable r) Aff (Either Unit o) e
mkArrayRenderer extras syntax each = Zuruzuru.Renderer \datums { add, output } ->
  HH.div [ HP.class_ $ H.ClassName "ast" ] $ pure $
  let postpend = add (Array.length datums) in
  if Array.null datums
  then HH.span_
      [ HH.text $ syntax (-1)
      , Inputs.inline_feather_button_action (Just postpend) "plus-square" "Add item"
      , HH.text $ syntax (-2)
      ]
  else HK.div [ HP.class_ $ H.ClassName "grid-container" ]
    let
      items = datums <#> \r ->
        renderArrayItems (SlottedHTML <<< HH.text <<< syntax) each (output <<< Left)
          (r { helpers { output = r.helpers.output <<< Left } })
      before = extras.before # mapWithIndex \i e ->
        Tuple ("before-"<>show i) $
          HH.div
          [ HP.class_ $ H.ClassName "row" ] $
            un SlottedHTML <<< map (output) <$> e
      after = extras.after # mapWithIndex \i e ->
        Tuple ("after-"<>show i) $
          HH.div
          [ HP.class_ $ H.ClassName "row" ] $
            un SlottedHTML <<< map (either (pure postpend) output) <$> e
    in before <> items <> after

renderArrayItems :: forall e r q.
  (Int -> SlottedHTML (Expandable r) Void) ->
  (Zuruzuru.Key -> e -> SlottedHTML (Expandable r) e) ->
  (Unit -> q) ->
  { helpers :: Zuruzuru.Helpers Unit q e
  , handle :: Zuruzuru.Handle' q
  , info :: Zuruzuru.ItemInfo' e
  } -> Tuple String (ExpandableHTML r q)
renderArrayItems syntax each output { helpers, handle, info } =
  let
    moving :: forall p i. HP.IProp ( style :: String | p ) i
    moving = HP.attr (H.AttrName "style") $
      "transform: translateY(" <> show info.offset <> "px)"
  in Tuple ("item-"<>info.key) $ HH.div [ HP.class_ $ H.ClassName "row" ]
  [ Inputs.inline_feather_button_action (Just (output unit))
    (if info.index == 0
    then "minimize"
    else "more-vertical")
    "Collapse"
  , HH.div_ [ un SlottedHTML $ absurd <$> syntax info.index ]
  , Inputs.icon_button_props
    [ moving
    , HP.ref handle.label
    , HE.onMouseDown handle.onMouseDown
    , HP.class_ (H.ClassName "move")
    , HP.tabIndex (-1)
    , HP.attr (H.AttrName "data-tooltip") "Reorder (drag/drop)"
    ] "menu" "feather inline active move vertical"
  , Inputs.inline_feather_button_props [ moving, HE.onClick (\_ -> Just helpers.remove), HP.attr (H.AttrName "data-tooltip") "Remove item" ] "minus-square"
  , HH.div [ moving ]
    [ un SlottedHTML $ each info.key info.value <#>
        helpers.set
    ]
  ]

annotated :: forall io annot r.
  (annot -> Star (SlottedHTML r) io (Either (annot -> annot) io)) ->
  Star (SlottedHTML r) (Tuple annot io) (Tuple annot io)
annotated f = Star \(Tuple annot io) ->
  case f annot of
    Star g -> g io <#> case _ of
      Left act -> Tuple (act annot) io
      Right o -> Tuple annot o

annotatedF :: forall f a annot r.
  (annot -> Star (SlottedHTML r) (f a) (Either (annot -> annot) (f a))) ->
  Star (SlottedHTML r) (EnvT annot f a) (EnvT annot f a)
annotatedF = _Newtype <<< annotated

type Listicle r o e =
  ( listicle :: H.Slot (Const Void) (Either (o -> o) (Dhall.Map.InsOrdStrMap e)) Slot
  , "UnionLit" :: H.Slot (Const Void) (Either (Either (o -> o) (Tuple String e)) (Dhall.Map.InsOrdStrMap e)) Slot
  , "ListLit" :: H.Slot (Const Void) (Either (Either (o -> o) (Maybe e)) (Array e)) Slot
  | r
  )

listicleSlot :: forall e o r r'. e -> (o -> Renderer r' (Tuple String e) (o -> o)) -> Slot ->
  RenderValue_ (SlottedHTML (Listicle r o e)) (EnvT o Dhall.Map.InsOrdStrMap e)
listicleSlot default renderer slot = annotatedF \o -> Star \i -> SlottedHTML $
  HH.slot (SProxy :: SProxy "listicle") slot listicleIOSM
    (Tuple { default, renderer: renderer o } i) pure

zz_map_o :: forall ps m o o' e.
  (o -> o') ->
  Zuruzuru.Renderer ps m o e ->
  Zuruzuru.Renderer ps m o' e
zz_map_o adapt (Zuruzuru.Renderer r) = Zuruzuru.Renderer
  \datums { add, output } ->
    r <@> { add, output: output <<< adapt } $ datums <#>
      \{ helpers, handle, info } ->
        { helpers: helpers { output = helpers.output <<< adapt }
        , handle, info
        }

type ExpandingListicle r o e = Expandable + Listicle r o e
type RenderComplex r annot a = Star
  (SlottedHTML (ExpandingListicle r (Collapsible annot) a))
type RenderComplexEnvT r annot a f = RenderComplex r annot a
  (EnvT (Collapsible annot) f a)
  (EnvT (Collapsible annot) f a)

type Collapsible annot = { collapsed :: Boolean | annot }
type Collapser annot = Collapsible annot -> Collapsible annot

collapsible :: forall r annot e o.
  SlottedHTML (ExpandingListicle r (Collapsible annot) e) Unit ->
  Zuruzuru.Renderer (ExpandingListicle r (Collapsible annot) e) Aff
    Unit
    o ->
  (Collapsible annot) ->
  Zuruzuru.Renderer (ExpandingListicle r (Collapsible annot) e) Aff
    (Collapser annot)
    o
collapsible collapsed renderer annot =
  zz_map_o collapse $
    if not annot.collapsed then renderer else
      Zuruzuru.Renderer \_ { output } ->
        un SlottedHTML $ output <$> collapsed
  where collapse _ r = r { collapsed = not r.collapsed }

newtype F a = F (VariantF (AST.AllTheThings Dhall.Map.InsOrdStrMap ()) a)
derive newtype instance functorF :: Functor F
type AnnotatedHoley =
  Cofree (Compose Maybe F) (Collapsible ())

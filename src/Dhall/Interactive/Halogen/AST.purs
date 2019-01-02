module Dhall.Interactive.Halogen.AST where

import Prelude

import Control.Comonad (extract)
import Control.Comonad.Cofree (Cofree)
import Control.Comonad.Env (EnvT(..))
import Control.Plus (empty)
import Data.Array as Array
import Data.Bifunctor (bimap, lmap)
import Data.Const (Const(..))
import Data.Either (Either(..), either)
import Data.Functor.App (App(..))
import Data.Functor.Compose (Compose(..))
import Data.Functor.Product (Product(..))
import Data.Functor.Variant (VariantF)
import Data.Functor.Variant as VariantF
import Data.FunctorWithIndex (mapWithIndex)
import Data.Identity (Identity(..))
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Maybe (Maybe(..))
import Data.Natural (intToNat, natToInt)
import Data.Newtype (class Newtype, un, unwrap, wrap)
import Data.Ord (lessThan, lessThanOrEq)
import Data.Profunctor (dimap)
import Data.Profunctor.Star (Star(..), hoistStar)
import Data.Profunctor.Strong (first, second)
import Data.Symbol (SProxy(..))
import Data.Tuple (Tuple(..), fst)
import Dhall.Core (S_, _S)
import Dhall.Core.AST as AST
import Dhall.Core.StrMapIsh as IOSM
import Dhall.Interactive.Halogen.Inputs (QueryExpanding)
import Dhall.Interactive.Halogen.Inputs as Inputs
import Dhall.Interactive.Halogen.Types (RenderValue_, RenderVariantF_', renderOnConst)
import Dhall.Interactive.Halogen.Types as Types
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
import Matryoshka (embed, project, transCata)
import Type.Row (type (+))

type Slot = Array String

newtype SlottedHTML r o = SlottedHTML (H.ComponentHTML' o r Aff)
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

renderLiterals ::
  forall i h ir or m a r. Functor h =>
  (SlottedHTML r ~> h) ->
  (i -> RenderVariantF_' h ir or a) ->
  (i -> RenderVariantF_' h (AST.Literals m ir) (AST.Literals m or) a)
renderLiterals render = identity
  >>> renderOnConst (_S::S_ "BoolLit")
    (Types.boolH # hoistStar (render <<< wrap))
  >>> renderOnConst (_S::S_ "NaturalLit")
    (Types.naturalH # hoistStar (render <<< wrap))
  >>> renderOnConst (_S::S_ "IntegerLit")
    (Types.intH # hoistStar (render <<< wrap))
  >>> renderOnConst (_S::S_ "DoubleLit")
    (Types.doubleH # hoistStar (render <<< wrap))

renderBuiltinTypes ::
  forall i h ir or m a r. Functor h =>
  (SlottedHTML r ~> h) ->
  (i -> RenderVariantF_' h ir or a) ->
  (i -> RenderVariantF_' h (AST.BuiltinTypes m ir) (AST.BuiltinTypes m or) a)
renderBuiltinTypes render = identity
  >>> Types.renderName (_S::S_ "Bool") named
  >>> Types.renderName (_S::S_ "Natural") named
  >>> Types.renderName (_S::S_ "Integer") named
  >>> Types.renderName (_S::S_ "Double") named
  >>> Types.renderName (_S::S_ "Text") named
  >>> Types.renderName (_S::S_ "List") named
  >>> Types.renderName (_S::S_ "Optional") named
  >>> Types.renderOnConst (_S::S_ "Const")
    (Star case _ of
      AST.Type -> render (wrap (HH.text "Type")) $> AST.Type
      AST.Kind -> render (wrap (HH.text "Kind")) $> AST.Kind
    )
  where named = render <<< wrap <<< HH.text

renderBuiltinFuncs ::
  forall i h ir or m a r. Functor h =>
  (SlottedHTML r ~> h) ->
  (i -> RenderVariantF_' h ir or a) ->
  (i -> RenderVariantF_' h (AST.BuiltinFuncs m ir) (AST.BuiltinFuncs m or) a)
renderBuiltinFuncs render = identity
  >>> Types.renderName (_S::S_ "NaturalFold") named
  >>> Types.renderName (_S::S_ "NaturalBuild") named
  >>> Types.renderName (_S::S_ "NaturalIsZero") named
  >>> Types.renderName (_S::S_ "NaturalEven") named
  >>> Types.renderName (_S::S_ "NaturalOdd") named
  >>> Types.renderName (_S::S_ "NaturalToInteger") named
  >>> Types.renderName (_S::S_ "NaturalShow") named
  >>> Types.renderName (_S::S_ "IntegerShow") named
  >>> Types.renderName (_S::S_ "IntegerToDouble") named
  >>> Types.renderName (_S::S_ "DoubleShow") named
  >>> Types.renderName (_S::S_ "ListBuild") named
  >>> Types.renderName (_S::S_ "ListFold") named
  >>> Types.renderName (_S::S_ "ListLength") named
  >>> Types.renderName (_S::S_ "ListHead") named
  >>> Types.renderName (_S::S_ "ListLast") named
  >>> Types.renderName (_S::S_ "ListIndexed") named
  >>> Types.renderName (_S::S_ "ListReverse") named
  >>> Types.renderName (_S::S_ "OptionalFold") named
  >>> Types.renderName (_S::S_ "OptionalBuild") named
  where named = render <<< wrap <<< HH.text

type LiftA2 f g = forall a b c.
  (f a -> f b -> f c) -> (g a -> g b -> g c)

renderBuiltinBinOps ::
  forall h ir or m a r. Functor h =>
  (SlottedHTML r ~> h) ->
  (LiftA2 (SlottedHTML r) h) ->
  Slot ->
  ((Slot -> RenderValue_ h a) -> RenderVariantF_' h ir or a) ->
  ((Slot -> RenderValue_ h a) -> RenderVariantF_' h (AST.BuiltinBinOps m ir) (AST.BuiltinBinOps m or) a)
renderBuiltinBinOps renderPure renderLiftA2 slot = identity
  >>> Types.renderOn (_S::S_ "BoolAnd") (renderBinOp renderPure renderLiftA2 slot "&&")
  >>> Types.renderOn (_S::S_ "BoolOr") (renderBinOp renderPure renderLiftA2 slot "||")
  >>> Types.renderOn (_S::S_ "BoolEQ") (renderBinOp renderPure renderLiftA2 slot "==")
  >>> Types.renderOn (_S::S_ "BoolNE") (renderBinOp renderPure renderLiftA2 slot "!=")
  >>> Types.renderOn (_S::S_ "NaturalPlus") (renderBinOp renderPure renderLiftA2 slot "+")
  >>> Types.renderOn (_S::S_ "NaturalTimes") (renderBinOp renderPure renderLiftA2 slot "*")
  >>> Types.renderOn (_S::S_ "TextAppend") (renderBinOp renderPure renderLiftA2 slot "++")
  >>> Types.renderOn (_S::S_ "ListAppend") (renderBinOp renderPure renderLiftA2 slot "#")
  >>> Types.renderOn (_S::S_ "Combine") (renderBinOp renderPure renderLiftA2 slot "∧")
  >>> Types.renderOn (_S::S_ "CombineTypes") (renderBinOp renderPure renderLiftA2 slot "⩓")
  >>> Types.renderOn (_S::S_ "Prefer") (renderBinOp renderPure renderLiftA2 slot "⫽")
  >>> Types.renderOn (_S::S_ "ImportAlt") (renderBinOp renderPure renderLiftA2 slot "?")

renderBinOp ::
  forall h a r. Functor h =>
  (SlottedHTML r ~> h) ->
  (LiftA2 (SlottedHTML r) h) ->
  Slot ->
  String ->
  (Slot -> RenderValue_ h a) ->
  RenderValue_ h (AST.Pair a)
renderBinOp renderPure renderLiftA2 slot op renderA =
  Star \(AST.Pair v0 v1) ->
    let
      t = Tuple v0 v1
      f r0 r1 = wrap $
        HH.span_ [ unwrap r0, HH.text (" " <> op <> " "), unwrap r1 ]
    in
    renderLiftA2 f
      (unwrap (first (renderA (slot <> ["first"]))) t)
      (unwrap (second (renderA (slot <> ["second"]))) t) <#>
      \(Tuple v0' v1') -> AST.Pair v0' v1'

overEnvT :: forall h annot a f g i. Functor h =>
  (i -> Star h (f a) (g a)) ->
  (i -> Star h (EnvT annot f a) (EnvT annot g a))
overEnvT f i = Star \(EnvT (Tuple annot f'a)) ->
  un Star (f i) f'a <#> \g'a -> EnvT (Tuple annot g'a)

renderBuiltinOps ::
  forall ir or a r.
  { default :: a } ->
  Slot ->
  ((Slot -> RenderValue_ (SlottedHTML (Expandable r)) a) -> RenderVariantF_' (SlottedHTML (Expandable r)) ir or a) ->
  ((Slot -> RenderValue_ (SlottedHTML (Expandable r)) a) -> RenderVariantF_' (SlottedHTML (Expandable r)) (AST.BuiltinOps IOSM.InsOrdStrMap ir) (AST.BuiltinOps IOSM.InsOrdStrMap or) a)
renderBuiltinOps { default } slot = renderBuiltinBinOps identity identity slot
  >>> Types.renderOn (_S::S_ "Field") renderField
  >>> Types.renderOn (_S::S_ "Constructors") renderConstructors
  >>> Types.renderOn (_S::S_ "BoolIf") renderBoolIf
  >>> Types.renderOn (_S::S_ "Merge") renderMerge
  >>> Types.renderOn (_S::S_ "Project") renderProject
  where
    renderField = \renderA -> Star \(Tuple field a) -> SlottedHTML $ HH.span_
      [ unwrap (Tuple field <$> unwrap (renderA (slot<>["fielded"])) a)
      , HH.text "."
      , HH.slot (SProxy :: SProxy "expanding") (slot<>["field"])
          (Inputs.expanding HP.InputText) field
          (Just <<< (Tuple <@> a))
      ]
    renderConstructors = \renderA -> Star \(Identity a) -> map Identity $ SlottedHTML $
      HH.span_ [ HH.text "constructors", HH.text " ", unwrap (unwrap (renderA slot) a) ]
    renderBoolIf = \renderA -> Star \(AST.Triplet c t f) -> SlottedHTML $ HH.span_
      [ HH.text "if "
      , unwrap $ unwrap (renderA (slot<>["c"])) c
        <#> \c' -> AST.Triplet c' t f
      , HH.text " then "
      , unwrap $ unwrap (renderA (slot<>["t"])) t
        <#> \t' -> AST.Triplet c t' f
      , HH.text " else "
      , unwrap $ unwrap (renderA (slot<>["f"])) f
        <#> \f' -> AST.Triplet c t f'
      ]
    renderMerge = \renderA -> Star \(AST.MergeF h v mty) -> SlottedHTML $ HH.span_
      case mty of
        Nothing ->
          [ HH.text "merge "
          , unwrap $ unwrap (renderA (slot<>["h"])) h
            <#> \h' -> AST.MergeF h' v mty
          , HH.text " "
          , unwrap $ unwrap (renderA (slot<>["v"])) v
            <#> \v' -> AST.MergeF h v' mty
          , Inputs.inline_feather_button_action (Just (AST.MergeF h v (Just default))) "type" "Add type"
          ]
        Just ty ->
          [ HH.text "merge "
          , unwrap $ unwrap (renderA (slot<>["h"])) h
            <#> \h' -> AST.MergeF h' v mty
          , HH.text " "
          , unwrap $ unwrap (renderA (slot<>["v"])) v
            <#> \v' -> AST.MergeF h v' mty
          , HH.text " : "
          , unwrap $ unwrap (renderA (slot<>["ty"])) ty
            <#> \ty' -> AST.MergeF h v (Just ty')
          , Inputs.inline_feather_button_action (Just (AST.MergeF h v Nothing)) "minus-circle" "Remove type"
          ]
    renderProject = \renderA -> Star \(Tuple (App fields) a) -> SlottedHTML $ HH.span_
      let
        -- Append extra empty field to allow adding more projections
        unFields = IOSM.unIOSM >>> map fst >>> (_ <> [""])
        -- And prune empty fields
        mkFields = IOSM.mkIOSM <<< map (Tuple <@> unit) <<< Array.filter (notEq "")
        render1 i field =
          HH.slot (SProxy :: SProxy "expanding") (slot<>[show i])
            (Inputs.expanding HP.InputText) field
            (map ((Tuple <@> a) <<< App <<< mkFields) <<< (Array.updateAt i <@> unFields fields))
      in
        [ unwrap (Tuple (App fields) <$> unwrap (renderA (slot<>["projected"])) a)
        , HH.text "."
        , HH.text "{"
        ] <> mapWithIndex render1 (unFields fields) <>
        [ HH.text "}"
        ]

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
      (H.Request (Const void)) -> absurd void
      (H.Handle (Left o) a) -> a <$ H.raise (Left o)
      (H.Handle (Right message) a) -> case message of
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
      H.ComponentHTML' (Either o (Zuruzuru.Message e))
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
  (IOSM.InsOrdStrMap e)

listicleIOSM :: forall r e o.
  H.Component HH.HTML (Const Void) (InputIOSM r e o) (Either o (IOSM.InsOrdStrMap e)) Aff
listicleIOSM = un ProComponent $ ProComponent listicle # dimap
  do bimap (\i -> i { default = Tuple mempty i.default }) IOSM.unIOSM
  do map IOSM.mkIOSM

type Expandable r =
  ( expanding :: H.Slot QueryExpanding String (Array String)
  | r
  )
type ExpandableHTML r a = H.ComponentHTML' a (Expandable r) Aff

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
  (Unit -> q Unit) ->
  { helpers :: Zuruzuru.Helpers Unit q (Tuple String e)
  , handle :: Zuruzuru.Handle' q
  , info :: Zuruzuru.ItemInfo' (Tuple String e)
  } -> Tuple String (ExpandableHTML r (q Unit))
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
  (Unit -> q Unit) ->
  { helpers :: Zuruzuru.Helpers Unit q e
  , handle :: Zuruzuru.Handle' q
  , info :: Zuruzuru.ItemInfo' e
  } -> Tuple String (ExpandableHTML r (q Unit))
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
  ( listicle :: H.Slot (Const Void) (Either (o -> o) (IOSM.InsOrdStrMap e)) Slot
  , "UnionLit" :: H.Slot (Const Void) (Either (Either (o -> o) (Tuple String e)) (IOSM.InsOrdStrMap e)) Slot
  , "ListLit" :: H.Slot (Const Void) (Either (Either (o -> o) (Maybe e)) (Array e)) Slot
  | r
  )

listicleSlot :: forall e o r r'. e -> (o -> Renderer r' (Tuple String e) (o -> o)) -> Slot ->
  RenderValue_ (SlottedHTML (Listicle r o e)) (EnvT o IOSM.InsOrdStrMap e)
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

renderIOSM :: forall a r annot.
  a -> Slot ->
  String -> String -> String -> String ->
  (Slot -> RenderComplex r annot a a a) ->
  RenderComplexEnvT r annot a IOSM.InsOrdStrMap
renderIOSM default slot pre rel sep post renderA =
  let
    renderer = zz_map_o (either identity absurd) $
      mkIOSMRenderer empty
        ((_ `lessThanOrEq` 0) >>> if _ then pre else sep) rel post
        \k -> unwrap (renderA [k])
    collapsed = SlottedHTML $ HH.span_
      [ HH.text pre
      , Inputs.inline_feather_button_action (Just unit) "maximize" "Expand"
      , HH.text post
      ]
  in listicleSlot default (collapsible collapsed renderer) slot

renderBuiltinTypes2 ::
  forall ir a r annot.
  { default :: a } ->
  Slot ->
  ((Slot -> RenderComplex r annot a a a) -> RenderComplexEnvT r annot a (VariantF ir)) ->
  ((Slot -> RenderComplex r annot a a a) -> RenderComplexEnvT r annot a (VariantF (AST.BuiltinTypes2 IOSM.InsOrdStrMap ir)))
renderBuiltinTypes2 { default } slot = identity
  >>> Types.renderOnAnnot (_S::S_ "Record") (renderIOSM default slot "{" ":" "," "}")
  >>> Types.renderOnAnnot (_S::S_ "Union") (renderIOSM default slot "<" ":" "|" ">")

renderLiterals2 ::
  forall ir a r annot.
  { default :: a } ->
  Slot ->
  ((Slot -> RenderComplex r annot a a a) -> RenderComplexEnvT r annot a (VariantF ir)) ->
  ((Slot -> RenderComplex r annot a a a) -> RenderComplexEnvT r annot a (VariantF (AST.Literals2 IOSM.InsOrdStrMap ir)))
renderLiterals2 { default } slot = identity
  >>> Types.renderOverAnnot (_S::S_ "None")
    (const $ Star $ const $ SlottedHTML $ HH.text "None")
  >>> Types.renderOverAnnot (_S::S_ "Some") renderSome
    -- FIXME: empty case will look like {} instead of {=}
  >>> Types.renderOnAnnot (_S::S_ "RecordLit") (renderIOSM default slot "{" "=" "," "}")
  >>> Types.renderOnAnnot (_S::S_ "UnionLit") renderUnionLit
  >>> Types.renderOnAnnot (_S::S_ "OptionalLit") renderOptionalLit
  >>> Types.renderOnAnnot (_S::S_ "ListLit") renderListLit
  >>> Types.renderOnAnnot (_S::S_ "TextLit") renderTextLit
  where
    renderSome = \renderA -> Star \(Identity a) -> map Identity $ SlottedHTML $
      HH.span_ [ HH.text "Some", HH.text " ", unwrap (unwrap (renderA slot) a) ]
    renderOptionalLit ::
      (Slot -> RenderComplex r annot a a a) ->
      RenderComplexEnvT r annot a (Product Identity Maybe)
    renderOptionalLit renderA = annotatedF $ \annot -> Star \(Product (Tuple (Identity ty) ma)) ->
      SlottedHTML $ HH.span_ $ join
        [ [ HH.text "[" ]
        , case ma of
            Nothing ->
              let added = Product (Tuple (Identity ty) (Just default)) in
              [ Inputs.inline_feather_button_action (Just (Right added)) "plus-square" "Add value"
              ]
            Just a ->
              let removed = Product (Tuple (Identity ty) Nothing) in
              [ HH.text " "
              , unwrap $ unwrap (renderA (slot <> ["OptionalLit value"])) a
                  <#> Right <<< \a' -> Product (Tuple (Identity ty) (Just a'))
              , HH.text " "
              , Inputs.inline_feather_button_action (Just (Right removed)) "minus-square" "Remove value"
              , HH.text " "
              ]
        , [ HH.text "]" ]
        , [ HH.text " : " ]
        , [ HH.text "Optional " ]
        , [ unwrap $ unwrap (renderA (slot <> ["OptionalLit type"])) ty
              <#> Right <<< \ty' -> Product (Tuple (Identity ty') ma)
          ]
        ]
    renderUnionLit ::
      (Slot -> RenderComplex r annot a a a) ->
      RenderComplexEnvT r annot a (Product (Tuple String) IOSM.InsOrdStrMap)
    renderUnionLit renderA = annotatedF \annot -> Star \(Product (Tuple (Tuple label a) tys)) ->
      let
        renderer =
          zz_map_o (lmap collapse) $
            if not annot.collapsed then openRenderer else
              Zuruzuru.Renderer \_ { output } ->
                un SlottedHTML $ output <$> collapsed
          where collapse (_ :: Unit) r = r { collapsed = not r.collapsed :: Boolean }

        adapt (Left (Left l)) = Left l
        adapt (Left (Right (Tuple label' a'))) =
          Right (Product (Tuple (Tuple label' a') tys))
        adapt (Right tys') =
          Right (Product (Tuple (Tuple label a) tys'))

        slotted = map adapt $ SlottedHTML $
          HH.slot (SProxy :: SProxy "UnionLit") slot listicleIOSM
            (Tuple { default, renderer: renderer } tys) pure
        -- FIXME: first line doesn't display when empty
        openRenderer = mkIOSMRenderer [firstLine]
          ((_ `lessThan` 0) >>> if _ then "|" else "|") ":" ">"
          \k -> unwrap (renderA [k])
        collapsed = SlottedHTML $ HH.span_
          [ HH.text "<"
          , Inputs.inline_feather_button_action (Just (Left unit)) "maximize" "Expand"
          , HH.text ">"
          ]
        firstLine = SlottedHTML <$>
          [ HH.div_ []
          , HH.div_ [ HH.text "<" ]
          , HH.div_ []
          , HH.div_ []
          , HH.span [ HP.class_ (H.ClassName "input-parent") ]
            [ HH.slot (SProxy :: SProxy "expanding") []
                (Inputs.expanding HP.InputText) label
                (Just <<< (Tuple <@> a))
            , HH.text "="
            , un SlottedHTML $ unwrap (renderA [""]) a <#>
                (Tuple label)
            ]
          ]
      in slotted
    renderListLit ::
      (Slot -> RenderComplex r annot a a a) ->
      RenderComplexEnvT r annot a (Product Maybe Array)
    renderListLit renderA = annotatedF \annot -> Star \(Product (Tuple mty vs)) ->
      let
        renderer =
          zz_map_o (lmap collapse) $
            if not annot.collapsed then openRenderer else
              Zuruzuru.Renderer \_ { output } ->
                un SlottedHTML $ output <$> collapsed
          where collapse (_ :: Unit) r = r { collapsed = not r.collapsed :: Boolean }

        adapt (Left (Left l)) = Left l
        adapt (Left (Right mty')) =
          Right (Product (Tuple mty' vs))
        adapt (Right vs') =
          Right (Product (Tuple mty vs'))

        slotted = map adapt $ SlottedHTML $
          HH.slot (SProxy :: SProxy "ListLit") slot listicle
            (Tuple { default, renderer } vs) pure
        openRenderer = mkArrayRenderer { before: [], after: [lastLine] }
          (\i -> if i == (-1) || i == 0 then "[" else if i == (-2) then "]" else ",")
          \k -> unwrap (renderA [k])
        collapsed = SlottedHTML $ HH.span_
          [ HH.text "["
          , Inputs.inline_feather_button_action (Just (Left unit)) "maximize" "Expand"
          , HH.text "]"
          ]
        lastLine = SlottedHTML <$>
          case mty of
            Nothing ->
              [ Inputs.inline_feather_button_action (Just (Right (Left unit))) "minimize" "Collapse"
              , HH.text "]"
              , Inputs.inline_feather_button_action (Just (Left unit)) "plus-square" "Append value"
              , Inputs.inline_feather_button_action (Just (Right (Right (Just default)))) "type" "Add type"
              ]
            Just ty ->
              [ Inputs.inline_feather_button_action (Just (Right (Left unit))) "minimize" "Collapse"
              , HH.div_ [ HH.text "]" ]
              , Inputs.inline_feather_button_action (Just (Left unit)) "plus-square" "Append value"
              , HH.div_ [ HH.text ":" ]
              , HH.span [ HP.class_ (H.ClassName "input-parent") ]
                [ un SlottedHTML $ unwrap (renderA [""]) ty <#>
                    (Right <<< Right <<< Just)
                ]
              ]
      in slotted
    renderTextLit ::
      (Slot -> RenderComplex r annot a a a) ->
      RenderComplexEnvT r annot a AST.TextLitF
    renderTextLit renderA = annotatedF \annot -> Star $ map Right <<< SlottedHTML <<<
      let
        renderString v =
          HH.textarea [ HE.onValueChange Just, HP.value v ]
        go i = case _ of
          AST.TextLit s ->
            [ renderString s <#> AST.TextLit
            , Inputs.inline_feather_button_action (Just (AST.TextInterp s default mempty)) "dollar-sign" "Add interpolated expression"
            ]
          AST.TextInterp s a t ->
            [ renderString s <#> (\s' -> AST.TextInterp s' a t)
            , un SlottedHTML $ unwrap (renderA (slot <> [show i])) a <#>
              (\a' -> AST.TextInterp s a' t)
            ] <> map (map (AST.TextInterp s a)) (go (i+one) t)
      in HH.div [ HP.class_ (H.ClassName "TextLit") ] <<< go (zero :: Int)

renderVariables ::
  forall ir a r annot.
  { default :: a } ->
  Slot ->
  ((Slot -> RenderComplex r annot a a a) -> RenderComplexEnvT r annot a (VariantF ir)) ->
  ((Slot -> RenderComplex r annot a a a) -> RenderComplexEnvT r annot a (VariantF (AST.Variable IOSM.InsOrdStrMap ir)))
renderVariables { default } slot = identity
  >>> Types.renderOverAnnot (_S::S_ "Var")
    (\_ -> _Newtype $ Star \(AST.V name ix) -> SlottedHTML $
      HH.span_
        [ un SlottedHTML $ expanding slot name \name' -> AST.V name' ix
        , HH.text "@"
        , unwrap Types.naturalH (intToNat ix)
          <#> \ix' -> AST.V name (natToInt ix')
        ]
    )
  >>> Types.renderOverAnnot (_S::S_ "Lam") (renderBindingBody "λ")
  >>> Types.renderOverAnnot (_S::S_ "Pi") (renderBindingBody "∀")
  >>> Types.renderOnAnnot (_S::S_ "Let") renderLet
  where
    renderBindingBody ::
      String ->
      (Slot -> RenderComplex r annot a a a) ->
      RenderComplex r annot a (AST.BindingBody a) (AST.BindingBody a)
    renderBindingBody syntax = \renderA ->
      Star \(AST.BindingBody name ty body) -> SlottedHTML $
        HH.span_
          [ HH.text syntax
          , HH.text "("
          , un SlottedHTML $ expanding slot name \name' -> AST.BindingBody name' ty body
          , HH.text " : "
          , unwrap $ unwrap (renderA (slot <> ["ty"])) ty
            <#> \ty' -> AST.BindingBody name ty' body
          , HH.text ")"
          , HH.text " -> "
          , unwrap $ unwrap (renderA (slot <> ["body"])) body
            <#> \body' -> AST.BindingBody name ty body'
          ]
    renderLet ::
      (Slot -> RenderComplex r annot a a a) ->
      RenderComplexEnvT r annot a AST.LetF
    renderLet = \renderA -> annotatedF \annot ->
      Star \(AST.LetF name mty value body) -> SlottedHTML $
        -- TODO: collapsability
        case mty of
          Nothing ->
            HH.span_
              [ HH.text "let "
              , un SlottedHTML $ expanding slot name \name' -> Right $ AST.LetF name' mty value body
              , Inputs.inline_feather_button_action (Just (Right (AST.LetF name (Just default) value body))) "type" "Add type"
              , HH.text " = "
              , unwrap $ unwrap (renderA (slot <> ["value"])) value
                <#> \value' -> Right $ AST.LetF name mty value' body
              , HH.text " in "
              , unwrap $ unwrap (renderA (slot <> ["body"])) body
                <#> \body' -> Right $ AST.LetF name mty value body'
              ]
          Just ty ->
            HH.span_
              [ HH.text "let "
              , un SlottedHTML $ expanding slot name \name' -> Right $ AST.LetF name' mty value body
              , HH.text " : "
              , unwrap $ unwrap (renderA (slot <> ["ty"])) ty
                <#> \ty' -> Right $ AST.LetF name (Just ty') value body
              , Inputs.inline_feather_button_action (Just (Right (AST.LetF name Nothing value body))) "minus-circle" "Remove type"
              , HH.text " = "
              , unwrap $ unwrap (renderA (slot <> ["value"])) value
                <#> \value' -> Right $ AST.LetF name mty value' body
              , HH.text " in "
              , unwrap $ unwrap (renderA (slot <> ["body"])) body
                <#> \body' -> Right $ AST.LetF name mty value body'
              ]

renderSyntax ::
  forall ir a r annot.
  { default :: a } ->
  Slot ->
  ((Slot -> RenderComplex r annot a a a) -> RenderComplexEnvT r annot a (VariantF ir)) ->
  ((Slot -> RenderComplex r annot a a a) -> RenderComplexEnvT r annot a (VariantF (AST.Syntax IOSM.InsOrdStrMap ir)))
renderSyntax { default } slot = identity
  >>> Types.renderOverAnnot (_S::S_ "App") (renderBinOp identity identity slot "·")
  >>> Types.renderOverAnnot (_S::S_ "Annot") (renderBinOp identity identity slot " : ")

renderSimpleThings ::
  forall r a i m.
  Slot -> i -> Types.RenderVariantF_ (SlottedHTML (Expandable r)) (AST.SimpleThings m ()) a
renderSimpleThings slot = Types.renderCase
  # renderLiterals identity
  # renderBuiltinTypes identity
  # renderBuiltinFuncs identity

renderFunctorThings ::
  forall r a annot.
  { default :: a } ->
  Slot ->
  (Slot -> RenderComplex r annot a a a) ->
  RenderComplexEnvT r annot a (VariantF (AST.FunctorThings IOSM.InsOrdStrMap ()))
renderFunctorThings { default } slot =
  overEnvT
  ( Types.renderCase
  # renderBuiltinOps { default } slot
  )
  # renderLiterals2 { default } slot
  # renderBuiltinTypes2 { default } slot
  # renderSyntax { default } slot
  # renderVariables { default } slot

renderAllTheThings ::
  forall r a annot.
  { default :: a } ->
  Slot ->
  (Slot -> RenderComplex r annot a a a) ->
  RenderComplexEnvT r annot a (VariantF (AST.AllTheThings IOSM.InsOrdStrMap ()))
renderAllTheThings { default } slot =
  overEnvT
  ( renderSimpleThings slot
  # renderBuiltinOps { default } slot
  )
  # renderLiterals2 { default } slot
  # renderBuiltinTypes2 { default } slot
  # renderSyntax { default } slot
  # renderVariables { default } slot

newtype F a = F (VariantF (AST.AllTheThings IOSM.InsOrdStrMap ()) a)
derive newtype instance functorF :: Functor F
type AnnotatedHoley =
  Cofree (Compose Maybe F) (Collapsible ())

toAnnotatedHoley :: AST.Expr IOSM.InsOrdStrMap Unit -> AnnotatedHoley
toAnnotatedHoley = transCata $ unwrap
  >>> VariantF.on (_S::S_ "Embed") (pure empty) (pure <<< F)
  >>> Compose >>> Tuple { collapsed: false } >>> EnvT

renderAnnotatedHoley ::
  Star
    (SlottedHTML (ExpandingListicle () (Collapsible ()) AnnotatedHoley))
    AnnotatedHoley
    AnnotatedHoley
renderAnnotatedHoley = go []
  where
    default :: AnnotatedHoley
    default = embed (EnvT (Tuple { collapsed: false } (Compose Nothing)))
    go slot = Star \i ->
      case project i of
        EnvT (Tuple annot (Compose Nothing)) ->
          SlottedHTML $ HH.text "_"
        EnvT (Tuple annot (Compose (Just (F layer)))) ->
          un Star (renderAllTheThings { default } slot go) (EnvT (Tuple annot layer))
          <#> \(EnvT (Tuple annot' layer')) ->
            EnvT (Tuple annot' (Compose (Just (F layer')))) # embed

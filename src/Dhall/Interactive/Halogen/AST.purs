module Dhall.Interactive.Halogen.AST where

import Prelude

import Control.Comonad (extract)
import Control.Comonad.Env (EnvT)
import Data.Array as Array
import Data.Bifunctor (bimap, lmap)
import Data.Const (Const(..))
import Data.Either (Either(..))
import Data.Functor.Compose (Compose(..))
import Data.Functor.Variant (VariantF)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Maybe (Maybe(..))
import Data.Natural (intToNat, natToInt)
import Data.Newtype (class Newtype, un, unwrap, wrap)
import Data.Profunctor.Star (Star(..), hoistStar)
import Data.Profunctor.Strong (first, second)
import Data.Symbol (class IsSymbol, SProxy(..))
import Data.Tuple (Tuple(..), fst)
import Data.Variant.Internal (FProxy)
import Dhall.Core (S_, _s)
import Dhall.Core.AST as AST
import Dhall.Core.StrMapIsh as IOSM
import Dhall.Interactive.Halogen.Inputs (QueryExpanding)
import Dhall.Interactive.Halogen.Inputs as Inputs
import Dhall.Interactive.Halogen.Types (RenderValue_, RenderVariantF_', renderOnConst)
import Dhall.Interactive.Halogen.Types as Types
import Effect.Aff (Aff)
import Halogen as H
import Halogen.Component as HC
import Halogen.HTML as HH
import Halogen.HTML.Elements.Keyed as HK
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.VDom.Thunk as Thunk
import Halogen.Zuruzuru as Zuruzuru
import Prim.Row as Row
import Type.Row (type (+))

type Slot = Array String

newtype SlottedHTML r o = SlottedHTML (H.ComponentHTML' o r Aff)
instance functorSlottedHTML :: Functor (SlottedHTML a) where
  map f (SlottedHTML h) =  SlottedHTML $ bimap mapSlot f h where
    mapSlot (HC.ComponentSlot s) = HC.ComponentSlot $ map f s
    mapSlot (HC.ThunkSlot s) = HC.ThunkSlot $ Thunk.hoist (lmap mapSlot) $ map f s
derive instance newtypeSlottedHTML :: Newtype (SlottedHTML a o) _

renderLiterals ::
  forall h ir or m a r. Functor h =>
  (SlottedHTML r ~> h) ->
  (RenderValue_ h a -> RenderVariantF_' h ir or a) ->
  (RenderValue_ h a -> RenderVariantF_' h (AST.Literals m ir) (AST.Literals m or) a)
renderLiterals render = identity
  >>> renderOnConst (_s::S_ "BoolLit")
    (Types.boolH # hoistStar (render <<< wrap))
  >>> renderOnConst (_s::S_ "NaturalLit")
    (Types.naturalH # hoistStar (render <<< wrap))
  >>> renderOnConst (_s::S_ "IntegerLit")
    (Types.intH # hoistStar (render <<< wrap))
  >>> renderOnConst (_s::S_ "DoubleLit")
    (Types.doubleH # hoistStar (render <<< wrap))

renderBuiltinTypes ::
  forall h ir or m a r. Functor h =>
  (SlottedHTML r ~> h) ->
  (RenderValue_ h a -> RenderVariantF_' h ir or a) ->
  (RenderValue_ h a -> RenderVariantF_' h (AST.BuiltinTypes m ir) (AST.BuiltinTypes m or) a)
renderBuiltinTypes render = identity
  >>> Types.renderName (_s::S_ "Bool") named
  >>> Types.renderName (_s::S_ "Natural") named
  >>> Types.renderName (_s::S_ "Integer") named
  >>> Types.renderName (_s::S_ "Double") named
  >>> Types.renderName (_s::S_ "Text") named
  >>> Types.renderName (_s::S_ "List") named
  >>> Types.renderName (_s::S_ "Optional") named
  where named = render <<< wrap <<< HH.text

renderBuiltinFuncs ::
  forall h ir or m a r. Functor h =>
  (SlottedHTML r ~> h) ->
  (RenderValue_ h a -> RenderVariantF_' h ir or a) ->
  (RenderValue_ h a -> RenderVariantF_' h (AST.BuiltinFuncs m ir) (AST.BuiltinFuncs m or) a)
renderBuiltinFuncs render = identity
  >>> Types.renderName (_s::S_ "NaturalFold") named
  >>> Types.renderName (_s::S_ "NaturalBuild") named
  >>> Types.renderName (_s::S_ "NaturalIsZero") named
  >>> Types.renderName (_s::S_ "NaturalEven") named
  >>> Types.renderName (_s::S_ "NaturalOdd") named
  >>> Types.renderName (_s::S_ "NaturalToInteger") named
  >>> Types.renderName (_s::S_ "NaturalShow") named
  >>> Types.renderName (_s::S_ "IntegerShow") named
  >>> Types.renderName (_s::S_ "IntegerToDouble") named
  >>> Types.renderName (_s::S_ "DoubleShow") named
  >>> Types.renderName (_s::S_ "ListBuild") named
  >>> Types.renderName (_s::S_ "ListFold") named
  >>> Types.renderName (_s::S_ "ListLength") named
  >>> Types.renderName (_s::S_ "ListHead") named
  >>> Types.renderName (_s::S_ "ListLast") named
  >>> Types.renderName (_s::S_ "ListIndexed") named
  >>> Types.renderName (_s::S_ "ListReverse") named
  >>> Types.renderName (_s::S_ "OptionalFold") named
  >>> Types.renderName (_s::S_ "OptionalBuild") named
  where named = render <<< wrap <<< HH.text

renderTerminals ::
  forall h ir or m a r. Functor h =>
  (SlottedHTML r ~> h) ->
  (RenderValue_ h a -> RenderVariantF_' h ir or a) ->
  (RenderValue_ h a -> RenderVariantF_' h (AST.Terminals m ir) (AST.Terminals m or) a)
renderTerminals render = identity
  >>> Types.renderOnConst (_s::S_ "Const")
    (Star case _ of
      AST.Type -> render (wrap (HH.text "Type")) $> AST.Type
      AST.Kind -> render (wrap (HH.text "Kind")) $> AST.Kind
    )
  >>> Types.renderOnConst (_s::S_ "Var")
    (Star \(AST.V name ix) ->
      let
        Tuple name' ix' =
          Tuple name (intToNat ix) #
            Types.renderProd Types.stringH Types.naturalH
      in render (wrap $ HH.span_ [ name', HH.text "@", ix' ]) <#>
        \(Tuple name'' ix'') -> AST.V name'' (natToInt ix'')
    )

type LiftA2 f g = forall a b c.
  (f a -> f b -> f c) -> (g a -> g b -> g c)

renderBuiltinBinOps ::
  forall h ir or m a r. Functor h =>
  (SlottedHTML r ~> h) ->
  (LiftA2 (SlottedHTML r) h) ->
  (RenderValue_ h a -> RenderVariantF_' h ir or a) ->
  (RenderValue_ h a -> RenderVariantF_' h (AST.BuiltinBinOps m ir) (AST.BuiltinBinOps m or) a)
renderBuiltinBinOps renderPure renderLiftA2 = identity
  >>> renderBinOp renderPure renderLiftA2 (_s::S_ "BoolAnd") "&&"
  >>> renderBinOp renderPure renderLiftA2 (_s::S_ "BoolOr") "||"
  >>> renderBinOp renderPure renderLiftA2 (_s::S_ "BoolEQ") "=="
  >>> renderBinOp renderPure renderLiftA2 (_s::S_ "BoolNE") "!="
  >>> renderBinOp renderPure renderLiftA2 (_s::S_ "NaturalPlus") "+"
  >>> renderBinOp renderPure renderLiftA2 (_s::S_ "NaturalTimes") "*"
  >>> renderBinOp renderPure renderLiftA2 (_s::S_ "TextAppend") "++"
  >>> renderBinOp renderPure renderLiftA2 (_s::S_ "ListAppend") "#"
  >>> renderBinOp renderPure renderLiftA2 (_s::S_ "Combine") "∧"
  >>> renderBinOp renderPure renderLiftA2 (_s::S_ "CombineTypes") "⩓"
  >>> renderBinOp renderPure renderLiftA2 (_s::S_ "Prefer") "⫽"
  >>> renderBinOp renderPure renderLiftA2 (_s::S_ "ImportAlt") "?"

renderBinOp ::
  forall h s ir or ir' or' a r.
    IsSymbol s =>
    Row.Cons s (FProxy AST.Pair) ir' ir =>
    Row.Cons s (FProxy AST.Pair) or' or =>
    Functor h =>
  (SlottedHTML r ~> h) ->
  (LiftA2 (SlottedHTML r) h) ->
  SProxy s ->
  String ->
  (RenderValue_ h a -> RenderVariantF_' h ir' or' a) ->
  (RenderValue_ h a -> RenderVariantF_' h ir or a)
renderBinOp renderPure renderLiftA2 s op = Types.renderOn s
  \renderA -> Star \(AST.Pair v0 v1) ->
    let
      t = Tuple v0 v1
      f r0 r1 = wrap $
        HH.span_ [ unwrap r0, HH.text (" " <> op <> " "), unwrap r1 ]
    in
    renderLiftA2 f (unwrap (first renderA) t) (unwrap (second renderA) t) <#>
      \(Tuple v0' v1') -> AST.Pair v0' v1'

type Renderer r e o = Zuruzuru.Renderer r Aff o (Tuple String e)
type State r e o =
  { default :: e
  , renderer :: Renderer r e o
  , values :: Array (Tuple String e)
  }
type IO = IOSM.InsOrdStrMap
type Input r e o = Tuple
  { default :: e
  , renderer :: Renderer r e o
  }
  (IO e)

listicle :: forall r e o.
  H.Component HH.HTML (Const Void) (Input r e o) (Either o (IO e)) Aff
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
          H.modify_ _ { values = v } <* H.raise (Right (IOSM.mkIOSM v))
        {-
        Zuruzuru.Added info -> a <$
          H.query (SProxy :: SProxy "zuruzuru") unit do
            Zuruzuru.queryInside (SProxy :: SProxy "expanding") [info.key] $
              Inputs.PassOn $ (TCHE.set (TCHE.Focused TC.empty) *> TCHE.get)
        -}
        _ -> pure a
  } where
    toState :: Input r e o -> State r e o
    toState (Tuple { default, renderer } (IOSM.InsOrdStrMap (Compose values))) =
      { default, renderer, values }

    render :: State r e o ->
      H.ComponentHTML' (Either o (Zuruzuru.Message (Tuple String e)))
        ( zuruzuru :: Zuruzuru.Slot'
          r
          Aff o (Tuple String e) Unit
        )
        Aff
    render st =
      HH.slot Zuruzuru._zuruzuru unit Zuruzuru.zuruzuru' (com st) lifting

    lifting (Left m) = Just (Right m)
    lifting (Right o) = Just (Left o)

    com :: State r e o -> Zuruzuru.Input' r Aff o (Tuple String e)
    com st =
      { values: st.values
      , direction: Zuruzuru.Vertical
      , default: pure (Tuple mempty st.default)
      , renderer: st.renderer
      }

type Expandable r =
  ( expanding :: H.Slot QueryExpanding String (Array String)
  | r
  )
type ExpandableHTML r a = H.ComponentHTML' a (Expandable r) Aff

mkRenderer :: forall e r.
  (Int -> String) ->
  String ->
  (Int -> e -> SlottedHTML (Expandable r) e) ->
  Zuruzuru.Renderer (Expandable r) Aff Unit (Tuple String e)
mkRenderer syntax close each = Zuruzuru.Renderer \datums { add, output } ->
  HH.div [ HP.class_ $ H.ClassName "ast" ] $ pure $
  let postpend = add (Array.length datums) in
  if Array.null datums
  then HH.span_
      [ HH.text $ syntax 0
      , Inputs.inline_feather_button_action (Just postpend) "plus-square"
      , HH.text close
      ]
  else HK.div [ HP.class_ $ H.ClassName "grid-container" ]
    let
      items = datums <#> renderItems (SlottedHTML <<< HH.text <<< syntax) each output
    in items <>
      [ Tuple "" $ HH.div
        [ HP.class_ $ H.ClassName "row" ]
        [ Inputs.inline_feather_button_action (Just (output unit)) "minimize"
        , HH.text close
        , Inputs.inline_feather_button_action (Just postpend) "plus-square"
        ]
      ]

renderItems :: forall e r q.
  (Int -> SlottedHTML (Expandable r) Void) ->
  (Int -> e -> SlottedHTML (Expandable r) e) ->
  (Unit -> q Unit) ->
  { helpers :: Zuruzuru.Helpers Unit q (Tuple String e)
  , handle :: Zuruzuru.Handle' q
  , info :: Zuruzuru.ItemInfo' (Tuple String e)
  } -> Tuple String (ExpandableHTML r (q Unit))
renderItems syntax each output { helpers, handle, info } =
  let
    moving :: forall p i. HP.IProp ( style :: String | p ) i
    moving = HP.attr (H.AttrName "style") $
      "transform: translateY(" <> show info.offset <> "px)"
  in Tuple info.key $ HH.div [ HP.class_ $ H.ClassName "row" ]
  [ Inputs.inline_feather_button_action (Just (output unit))
    if info.index == 0
    then "minimize"
    else "more-vertical"
  , HH.div_ [ un SlottedHTML $ absurd <$> syntax info.index ]
  , Inputs.icon_button_props
    [ moving
    , HP.ref handle.label
    , HE.onMouseDown handle.onMouseDown
    , HP.class_ (H.ClassName "move")
    , HP.tabIndex (-1)
    ] "menu" "feather inline active move vertical"
  , Inputs.inline_feather_button_props [ moving, HE.onClick (\_ -> Just helpers.remove) ] "minus-square"
  , HH.span [ HP.class_ (H.ClassName "input-parent"), moving ]
    [ HH.slot (SProxy :: SProxy "expanding") [info.key]
        (Inputs.expanding HP.InputText) (fst info.value)
        (Just <<< (Tuple <@> extract info.value) >>> helpers.set)
    , un SlottedHTML $ each info.index (extract info.value) <#>
        (Tuple (fst info.value) >>> helpers.set)
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
  | r
  )

listicleSlot :: forall e o r r'. e -> (o -> Renderer r' e (o -> o)) -> Slot ->
  RenderValue_ (SlottedHTML (Listicle r o e)) (EnvT o IOSM.InsOrdStrMap e)
listicleSlot default renderer slot = annotatedF \o -> Star \i -> SlottedHTML $
  HH.slot (SProxy :: SProxy "listicle") slot listicle
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
type RenderComplex r annot a = Star (SlottedHTML (ExpandingListicle r { collapsed :: Boolean | annot } a))
type RenderComplexEnvT r annot a f = RenderComplex r annot a
  (EnvT { collapsed :: Boolean | annot } f a)
  (EnvT { collapsed :: Boolean | annot } f a)

renderBuiltinTypes2 ::
  forall ir a r annot.
  { default :: a } ->
  Slot ->
  (RenderComplex r annot a a a -> RenderComplexEnvT r annot a (VariantF ir)) ->
  (RenderComplex r annot a a a -> RenderComplexEnvT r annot a (VariantF (AST.BuiltinTypes2 IOSM.InsOrdStrMap ir)))
renderBuiltinTypes2 { default } slot = identity
  >>> Types.renderOnAnnot (_s::S_ "Record") (renderIOSM "{" ":" "," "}")
  >>> Types.renderOnAnnot (_s::S_ "Union") (renderIOSM "<" ":" "|" ">")
  where
    renderIOSM pre rel sep post renderA =
      let
        renderer = mkRenderer (eq 0 >>> if _ then pre else sep) post \_ -> unwrap renderA
        collapsed :: forall s io. Zuruzuru.Renderer s Aff Unit io
        collapsed = Zuruzuru.Renderer \_ { output } -> HH.span_
          [ HH.text pre
          , Inputs.inline_feather_button_action (Just (output unit)) "plus-square"
          , HH.text post
          ]
        annotatedRenderer annot =
          if not annot.collapsed then renderer
          else collapsed
        collapse _ r = r { collapsed = not r.collapsed }
      in listicleSlot default (zz_map_o collapse <<< annotatedRenderer) slot

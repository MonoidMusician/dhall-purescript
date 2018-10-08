module Dhall.Interactive where

import Prelude

import Control.Coroutine (consumer)
import Control.Monad.Free (Free)
import Control.Monad.Free as Free
import Data.Array as Array
import Data.Const (Const(..))
import Data.Either (Either(..), either)
import Data.Functor.Variant (FProxy, VariantF)
import Data.Functor.Variant as VariantF
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, unwrap, wrap)
import Data.Profunctor (dimap)
import Data.Profunctor.Star (Star(..))
import Data.Symbol (SProxy(..))
import Data.Tuple (Tuple(..))
import Dhall.Core.AST as AST
import Dhall.Interactive.Halogen.Inputs as Inputs
import Dhall.Interactive.Halogen.Types as Types
import Dhall.Interactive.Types (InteractiveExpr, Annotation)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class.Console (logShow)
import Halogen as H
import Halogen.Aff as HA
import Halogen.Expanding as TCHE
import Halogen.HTML as HH
import Halogen.HTML.Elements.Keyed as HK
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.VDom.Driver (runUI)
import Halogen.Zuruzuru as Zuruzuru
import Matryoshka (cata)
import Unsafe.Coerce (unsafeCoerce)
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

type Natural = Int
type ExprRow =
  ( "NaturalLit" :: AST.CONST Natural
  , "NaturalPlus" :: FProxy AST.Pair
  -- , "NaturalTimes" :: FProxy AST.Pair
  )
newtype Expr a = Expr (Free (VariantF ExprRow) a)
derive instance newtypeExpr :: Newtype (Expr a) _

instance showExpr :: Show a => Show (Expr a) where
  show a = show (unsafeCoerce a :: InteractiveExpr Annotation)

mkNaturalLit :: forall a. Int -> Expr a
mkNaturalLit n = Expr $ Free.wrap $
  VariantF.inj (SProxy :: SProxy "NaturalLit") $ Const n

mkNaturalPlus :: forall a. Expr a -> Expr a -> Expr a
mkNaturalPlus l r = Expr $ Free.wrap $
  VariantF.inj (SProxy :: SProxy "NaturalPlus") $ map unwrap $ AST.Pair l r

rNaturalPlus :: forall ir or a.
  (Types.RenderValue a -> Types.RenderVariantF' ir or a) ->
  Types.RenderValue a ->
  Types.RenderVariantF'
    ( "NaturalPlus" :: FProxy AST.Pair | ir )
    ( "NaturalPlus" :: FProxy AST.Pair | or ) a
rNaturalPlus = Types.renderOn (SProxy :: SProxy "NaturalPlus")
  \a -> Star \p ->
    let AST.Pair l r = Types.renderPair a p in
    HH.span_ [ l, HH.text "+", r ]

rExpr1 :: forall a. Types.RenderValue a -> Types.RenderValue (VariantF ExprRow a)
rExpr1 = rNaturalPlus $ Types.renderOn (SProxy :: SProxy "NaturalLit")
  (const $ dimap unwrap wrap $ Types.naturalH) $ Types.renderCase

rExpr' :: Types.RenderValue (Free (VariantF ExprRow) Void)
rExpr' = Star \f -> case Free.resume f of
  Left l -> Free.wrap <$> (unwrap (rExpr1 rExpr') l)
  Right r -> absurd r

rExpr :: Types.RenderValue (Expr Void)
rExpr = case rExpr' of
  Star s -> Star \e ->
    HH.div [ HP.class_ $ H.ClassName "ast" ]
     [ map wrap $ s $ unwrap e ]

example :: Expr Void
example = mkNaturalPlus (mkNaturalLit 2) (mkNaturalLit 2)

eval :: Expr Void -> Expr Void
eval = (<<<) mkNaturalLit $ (>>>) unwrap $ cata $ (>>>) unwrap $ either absurd $
  VariantF.case_
  # VariantF.on (SProxy :: SProxy "NaturalLit") unwrap
  # VariantF.on (SProxy :: SProxy "NaturalPlus")
    (\(AST.Pair l r) -> l + r)

main :: Effect Unit
main = HA.runHalogenAff do
  body <- HA.awaitBody
  driver <- runUI interactive unit body
  driver2 <- runUI (Types.simpleC rExpr) example body
  driver2.subscribe $ consumer \v ->
    mempty <$ logShow v <* logShow (eval v)
  pure unit

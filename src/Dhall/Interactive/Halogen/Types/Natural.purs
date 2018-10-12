module Dhall.Interactive.Halogen.Types.Natural where

import Prelude

import Control.Monad.Free (Free)
import Data.Array as Array
import Data.Bifunctor (lmap)
import Data.Foldable (traverse_)
import Data.Functor.Variant (SProxy(..))
import Data.Int as Int
import Data.Maybe (Maybe(..), isJust)
import Data.Natural (Natural, intToNat)
import Data.Profunctor (dimap)
import Data.String as String
import Data.Tuple (Tuple(..))
import Dhall.Interactive.Halogen.Inputs as Inputs
import Dhall.Interactive.Halogen.Types (InOut(..), DataComponent)
import Effect.Class (class MonadEffect)
import Halogen as H
import Halogen.Expanding (expandingComponent)
import Halogen.Expanding as TCHE
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Web.Util.TextCursor as TC

{-
naturalH :: RenderValue Natural
naturalH = Star \v -> HH.input
  [ HP.type_ InputNumber
  , HP.min zero
  , HP.step (Step one)
  , HP.value (show v)
  , HE.onValueInput (Int.fromString >>> map intToNat)
  ]
-}

type Query = InOut Natural
type State = TCHE.Blurry

type Slots =
  ( expanding :: H.Slot (Free TCHE.Query) TCHE.Blurry Unit
  )

parse :: String -> Maybe Natural
parse = Int.fromString >>> map intToNat

component :: forall m. MonadEffect m => DataComponent Natural m
component = H.mkComponent { initialState, render, eval } where
  initialState :: Natural -> State
  initialState = TCHE.Blurred <<< show

  putNat v = H.modify_ case _ of
      TCHE.Blurred _ -> TCHE.Blurred $ show v
      TCHE.Focused _ -> TCHE.Focused $ TC.single TC._selected $ show v

  render :: State -> H.ComponentHTML' TCHE.Blurry Slots m
  render b =
    HH.slot (SProxy :: SProxy "expanding") unit expandingComponent
      (Tuple (Inputs.settings HP.InputText) b) pure

  eval :: H.HalogenQ Query TCHE.Blurry Natural ~>
    H.HalogenM' State TCHE.Blurry Slots Natural m
  eval (H.Initialize a) = pure a
  eval (H.Finalize a) = pure a
  eval (H.Receive v a) = a <$ do
    b <- H.get
    let cur = parse $ TCHE.toString b
    when (Just v /= cur) $ putNat v
  eval (H.Handle b a) = a <$ do
    let Tuple b' mn = handleB b
    b_ <- H.get
    when (b' /= b_) do
      H.put b'
      traverse_ H.raise mn
  eval (H.Request q) = case q of
    In a v -> putNat v $> a
    Out a v -> H.raise v $> a

  handleB :: TCHE.Blurry -> Tuple TCHE.Blurry (Maybe Natural)
  handleB (TCHE.Blurred s) = lmap (TCHE.Blurred <<< TC.content)
    (handle (TC.single TC._selected s))
  handleB (TCHE.Focused tc) = lmap TCHE.Focused (handle tc)

  reject :: String -> String
  reject =
    let nums = String.toCodePointArray "0123456789"
    in dimap String.toCodePointArray String.fromCodePointArray $
      Array.filter \c -> isJust (Array.elemIndex c nums)

  handle :: TC.TextCursor -> Tuple TC.TextCursor (Maybe Natural)
  handle tc | tc == TC.empty = Tuple (TC.single TC._selected "0") (Just zero)
  handle tc = tc # TC._all reject >>> (Tuple <*> parse <<< TC.content)

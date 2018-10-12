module Dhall.Interactive.Halogen.Types where

import Prelude

import Control.Apply (lift2)
import Data.Bifunctor (bimap)
import Data.Function (on)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Variant (FProxy, SProxy, VariantF)
import Data.Functor.Variant as VariantF
import Data.Int (fromString) as Int
import Data.Maybe (Maybe(..))
import Data.Natural (Natural, intToNat, natToInt)
import Data.Newtype (un, unwrap)
import Data.Number (fromString) as Number
import Data.Ord (abs, signum)
import Data.Profunctor.Star (Star(..))
import Data.Profunctor.Strong (first, second)
import Data.Symbol (class IsSymbol)
import Data.Tuple (Tuple(..), uncurry)
import Dhall.Core.AST (Pair(..))
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties (InputType(..), StepValue(..))
import Halogen.HTML.Properties as HP
import Prim.Row as Row
import Unsafe.Coerce (unsafeCoerce)

type RenderValue_ h v = RenderValue_' h v v
type RenderValue_' h = Star h
type RenderVariantF_ h r a = RenderVariantF_' h r r a
type RenderVariantF_' h ir or a = RenderValue_' h (VariantF ir a) (VariantF or a)

type RenderValue v = RenderValue' v v
type RenderValue' = Star (HH.HTML Void)
type RenderVariantF r a = RenderVariantF' r r a
type RenderVariantF' ir or a = RenderValue' (VariantF ir a) (VariantF or a)

renderCase :: forall a or. RenderValue a -> RenderVariantF' () or a
renderCase _ = Star VariantF.case_

renderOn ::
  forall s f ir or ir' or' a h.
    IsSymbol s =>
    Functor h =>
    Functor f =>
    Row.Cons s (FProxy f) ir' ir =>
    Row.Cons s (FProxy f) or' or =>
  SProxy s ->
  (RenderValue_ h a -> RenderValue_ h (f a)) ->
  (RenderValue_ h a -> RenderVariantF_' h ir' or' a) ->
  (RenderValue_ h a -> RenderVariantF_' h ir or a)
renderOn s h r a = Star $ VariantF.on s
  (unwrap $ map (VariantF.inj s) $ h a)
  (unwrap $ map unsafeCoerce $ r a)

renderProd :: forall a b h. Functor h =>
  RenderValue_ h a ->
  RenderValue_ h b ->
  Tuple a b ->
  Tuple (h (Tuple a b)) (h (Tuple a b))
renderProd a b t = Tuple
  (unwrap (first a) t)
  (unwrap (second b) t)

renderProdC :: forall a b h m. Applicative m => Functor h =>
  RenderValue_ (Compose m h) a ->
  RenderValue_ (Compose m h) b ->
  Tuple a b ->
  m (Tuple (h (Tuple a b)) (h (Tuple a b)))
renderProdC a b t = uncurry (lift2 Tuple `on` un Compose) $ renderProd a b t

renderPair :: forall a h. Functor h =>
  RenderValue_ h a ->
  Pair a ->
  Pair (h (Pair a))
renderPair a (Pair l r) =
  let Tuple l' r' = renderProd a a (Tuple l r) in
  Pair l' r' <#> map \(Tuple l'' r'') -> Pair l'' r''

renderPairC :: forall a h m. Applicative m => Functor h =>
  RenderValue_ (Compose m h) a ->
  Pair a ->
  m (Pair (h (Pair a)))
renderPairC a (Pair l r) =
  renderProdC a a (Tuple l r) <#> \(Tuple l' r') ->
    Pair l' r' <#> map \(Tuple l'' r'') -> Pair l'' r''

naturalH :: RenderValue Natural
naturalH = Star \v -> HH.input
  [ HP.type_ InputNumber
  , HP.min zero
  , HP.step (Step one)
  , HP.value (show v)
  , HE.onValueInput (Int.fromString >>> map intToNat)
  ]

boolH :: RenderValue Boolean
boolH = Star \v ->
  HH.button [ HE.onClick (pure (pure (not v))) ]
    [ HH.text if v then "True" else "False" ]

intH :: RenderValue Int
intH = Star \v -> HH.span_
  [ HH.button [ HE.onClick (pure (pure (negate v))) ]
    [ HH.text if v < 0 then "-" else "+" ]
  , unwrap naturalH (intToNat v) <#> natToInt >>> mul (signum v)
  ]

stringH :: RenderValue String
stringH = Star \v -> HH.input
  [ HP.type_ InputText
  , HP.value v
  , HE.onValueInput pure
  ]

doubleH :: RenderValue Number
doubleH = Star \v -> HH.input
  [ HP.type_ InputNumber
  , HP.step (Step 0.5)
  , HP.value (show (abs v))
  , HE.onValueInput Number.fromString
  ]

data InOut v a = In a v | Out a v

type DataSlot v = H.Slot (InOut v) v Int
type DataComponent v = H.Component HH.HTML (InOut v) v v

simpleC :: forall v m. RenderValue v -> DataComponent v m
simpleC renderer = H.component
  { initializer: Nothing
  , finalizer: Nothing
  , receiver: Just <<< In unit
  , initialState: identity
  , eval: case _ of
      In a v -> a <$ H.put v
      Out a v -> a <$ H.put v <* H.raise v
  , render: bimap absurd (Out unit) <<< unwrap renderer
  }

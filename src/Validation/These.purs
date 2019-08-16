module Validation.These where

import Prelude

import Control.Comonad (extract)
import Control.Monad.Writer as W
import Control.Plus (empty)
import Data.Array.NonEmpty as NEA
import Data.Bifunctor (class Bifunctor)
import Data.Foldable (class Foldable, foldMap, foldlDefault, foldrDefault)
import Data.Functor.Compose (Compose(..))
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))

-- | Yet another alternative validation type, this one uses two layers of
-- | NonEmptyArray instead of a generic/free Semiring, in order to guarantee
-- | that an error is actually thrown. Thus it does not provide `empty`; you
-- | must supply your own error for a failure case.
-- |
-- | There is no need for a monad transformer like this because this isn't a
-- | monad, and applicatives `Compose`.
data Erroring e a
  = Success a
  | Error (NEA.NonEmptyArray e) (Maybe a)

derive instance eqErroring :: (Eq e, Eq a) => Eq (Erroring e a)

instance showErroring :: (Show e, Show a) => Show (Erroring e a) where
  show (Success a) = "(Success " <> show a <> ")"
  show (Error es ma) = "(Error " <> show es <> " " <> show ma <> ")"

instance foldableErroring :: Foldable (Erroring e) where
  foldMap f (Success a) = f a
  foldMap f (Error _ ma) = foldMap f ma
  foldl f = foldlDefault f
  foldr f = foldrDefault f

instance functorErroring :: Functor (Erroring e) where
  map f (Success a) = Success (f a)
  map f (Error e ma) = Error e (map f ma)

instance bifunctorErroring :: Bifunctor Erroring where
  bimap _ g (Success a) = Success (g a)
  bimap f g (Error e ma) = Error (map f e) (map g ma)

instance applyErroring :: Apply (Erroring e) where
  apply (Success f) (Success a) = Success (f a)
  apply (Error es mf) (Success a) = Error es (mf <@> a)
  apply (Success f) (Error es ma) = Error es (f <$> ma)
  apply (Error e1s mf) (Error e2s ma) = Error (e1s <> e2s) (mf <*> ma)

instance applicativeErroring :: Applicative (Erroring e) where
  pure = Success

-- | The `Bind` instance can only take the error from the first computation if it
-- | errors, so it is not compatible with the `Apply` instance, and thus does
-- | not form a `Monad`. Moral of the story: Use `<*>` when possible!
instance bindErroring :: Bind (Erroring e) where
  bind (Success a) f = f a
  bind (Error es Nothing) _ = Error es Nothing
  bind (Error es (Just a)) f = case f a of
    Success a' -> Error es (Just a')
    Error es' ma' -> Error (es <> es') ma'

confirm :: forall a b e. a -> Erroring e b -> Erroring e a
confirm a (Success _) = Success a
confirm a (Error es _) = Error es (Just a)

confirmW :: forall w a b e. Monoid w => a -> W.WriterT w (Erroring e) b -> W.WriterT w (Erroring e) a
confirmW a = case _ of
  W.WriterT (Success (Tuple _ accum)) ->
    W.WriterT (Success (Tuple a accum))
  W.WriterT (Error es mtaccum) ->
    W.WriterT (Error es $ pure $ Tuple a $ foldMap extract mtaccum)

mconfirmW :: forall w a e. Monoid w => Maybe a -> W.WriterT w (Erroring e) a -> W.WriterT w (Erroring e) a
mconfirmW = case _ of
  Nothing -> identity
  Just a -> confirmW a

--------------------------------------------------------------------------------

-- | Return the value inside the `Maybe` or throw the provide error.
note :: forall e a. e -> Maybe a -> Erroring e a
note _ (Just a) = pure a
note e Nothing = erroring e

-- | Throw an error if the result is `Nothing`.
onFailure :: forall e a. e -> Erroring e (Maybe a) -> Erroring e a
onFailure e c = c >>= note e

hush :: forall e a. Erroring e a -> Maybe a
hush (Error _ ma) = ma
hush (Success a) = pure a

hush' :: forall e a. Erroring e a -> Maybe a
hush' (Error _ _) = Nothing
hush' (Success a) = pure a

-- | Throw an error! No frills.
erroring :: forall e a. e -> Erroring e a
erroring = (Error <@> empty) <<< pure

-- | Throw an error, but let the computation continue with a known result anyways.
erroringBut :: forall e a. e -> a -> Erroring e a
erroringBut e a = Error (pure e) (pure a)

--------------------------------------------------------------------------------

-- | Lift from Errors to Feedback, ERrors to FeedbackR
liftW :: forall f a m. Functor f => Monoid m => f a -> W.WriterT m f a
liftW m = W.WriterT (Tuple <$> m <@> mempty)

unW :: forall f a m. Functor f => W.WriterT m f a -> f a
unW (W.WriterT m) = m <#> \(Tuple a _) -> a

hushW :: forall m e a. W.WriterT m (Erroring e) a -> Maybe a
hushW (W.WriterT (Error _ ma)) = ma <#> \(Tuple a _) -> a
hushW (W.WriterT (Success (Tuple a _))) = pure a

hushW' :: forall m e a. W.WriterT m (Erroring e) a -> Maybe a
hushW' (W.WriterT (Error _ _)) = Nothing
hushW' (W.WriterT (Success (Tuple a _))) = pure a

liftCL :: forall f g. Functor f => Applicative g => f ~> Compose f g
liftCL = Compose <<< map pure

liftCR :: forall f g. Applicative f => g ~> Compose f g
liftCR = Compose <<< pure

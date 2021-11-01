module Dhall.Lib.MonoidalState where

import Prelude

import Control.Apply (lift2)
import Control.Comonad (extract)
import Control.Monad.Writer as W
import Control.Plus (class Plus, empty)
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Bifoldable (bifoldMap)
import Data.Bifunctor (class Bifunctor, bimap)
import Data.Either (Either(..), either)
import Data.Functor.Compose (Compose(..))
import Data.Map (Map, SemigroupMap(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Monoid.Disj (Disj(..))
import Data.Semigroup.Foldable (class Foldable1, foldMap1, foldl1Default, foldr1Default)
import Data.Semigroup.Traversable (class Traversable1, sequence1, traverse1)
import Data.These (These(..), theseLeft, theseRight)
import Data.Traversable (class Foldable, class Traversable, foldMap, foldl, foldr, sequence, traverse)
import Data.Tuple (Tuple(..))
import Dhall.Map as Dhall.Map
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)


newtype EitherA e a = EitherA (Either e a)
derive newtype instance functorEitherA :: Functor (EitherA e)
derive newtype instance bifunctorEitherA :: Bifunctor EitherA
instance applyEitherA :: Semigroup e => Apply (EitherA e) where
  apply (EitherA (Right f)) (EitherA (Right a)) = EitherA (Right (f a))
  apply (EitherA (Left e1)) (EitherA (Left e2)) = EitherA (Left (e1 <> e2))
  apply (EitherA (Left e)) (EitherA (Right _)) = EitherA (Left e)
  apply (EitherA (Right _)) (EitherA (Left e)) = EitherA (Left e)
instance applicativeEitherA :: Semigroup e => Applicative (EitherA e) where
  pure = EitherA <<< Right
instance bindEitherA :: Semigroup e => Bind (EitherA e) where
  bind (EitherA (Left e)) _ = EitherA (Left e)
  bind (EitherA (Right a)) f = f a

class Applicative f <= PartialSemigroup f m where
  pappend :: m -> m -> f m

class PartialSemigroup f m <= PartialMonoid f m where
  pempty :: Proxy f -> m


purempty :: forall f m. PartialMonoid f m => f m
purempty = pure $ pempty (Proxy :: Proxy f)

instance partialSemigroupMap :: (Ord k, PartialSemigroup f m) => PartialSemigroup f (SemigroupMap k m) where
  pappend (SemigroupMap m1s) (SemigroupMap m2s) = map SemigroupMap $ sequence $ (_ $ m2s) $ (_ $ m1s) $
    Dhall.Map.unionWithMapThese \_ -> case _ of
      This m1 -> Just (pure m1)
      That m2 -> Just (pure m2)
      Both m1 m2 -> Just (pappend m1 m2)

instance partialMonoidSemigroupMap :: (Ord k, PartialSemigroup f m) => PartialMonoid f (SemigroupMap k m) where
  pempty = pure $ SemigroupMap Map.empty

instance partialSemigroupTuple :: (PartialSemigroup f a, PartialSemigroup f b) => PartialSemigroup f (Tuple a b) where
  pappend (Tuple a0 b0) (Tuple a1 b1) = lift2 Tuple (pappend a0 a1) (pappend b0 b1)

instance partialMonoidTuple :: (PartialMonoid f a, PartialMonoid f b) => PartialMonoid f (Tuple a b) where
  pempty _ = Tuple (pempty (Proxy :: Proxy f)) (pempty (Proxy :: Proxy f))

newtype PartialMap :: Type -> (Type -> Type) -> Type -> Type
newtype PartialMap k f m = PartialMap (Map k (f m))

instance semigroupPartialMap :: (Ord k, PartialSemigroup f m, Bind f) => Semigroup (PartialMap k f m) where
  append (PartialMap m1s) (PartialMap m2s) = PartialMap $ (_ $ m2s) $ (_ $ m1s) $
    Dhall.Map.unionWithMapThese \_ -> case _ of
      This m1 -> Just (m1)
      That m2 -> Just (m2)
      Both m1 m2 -> Just (join $ pappend <$> m1 <*> m2)

instance monoidPartialMap :: (Ord k, PartialSemigroup f m, Bind f) => Monoid (PartialMap k f m) where
  mempty = PartialMap Map.empty

newtype Total m = Total m
derive newtype instance semigroupTotal :: Semigroup m => Semigroup (Total m)
derive newtype instance monoidTotal :: Monoid m => Monoid (Total m)
instance partialSemigroupTotal :: (Applicative f, Semigroup m) => PartialSemigroup f (Total m) where
  pappend a b = pure (append a b)
instance partialMonoidTotal :: (Applicative f, Monoid m) => PartialMonoid f (Total m) where
  pempty = pure mempty
instance errorSemigroupTotal :: Semigroup m => ErrorSemigroup Void (Total m) (Total m) where
  split = That
  ocomb = absurd
  mcomb = identity
instance errorMonoidTotal :: Monoid m => ErrorMonoid Void (Total m) (Total m) where
  emempty = pure mempty

newtype Untotal :: (Type -> Type) -> Type -> Type
newtype Untotal f m = Untotal (f m)
instance partialSemigroupUntotal :: PartialSemigroup f m => PartialSemigroup f (Untotal f m) where
  pappend (Untotal a) (Untotal b) = map Untotal $ lift2 pappend a b
instance partialMonoidUntotal :: PartialMonoid f m => PartialMonoid f (Untotal f m) where
  pempty = pure $ Untotal purempty
instance semigroupUntotal ::(PartialSemigroup f m, Bind f) => Semigroup (Untotal f m) where
  append (Untotal a) (Untotal b) = Untotal $ join $ lift2 pappend a b
instance monoidUntotal :: (PartialMonoid f m, Bind f) => Monoid (Untotal f m) where
  mempty = Untotal purempty

newtype PWriterT w m a = PWriterT (m (Tuple w a))
instance functorPWriterT :: Functor m => Functor (PWriterT w m) where
  map f (PWriterT ma) = PWriterT (map (map f) ma)
instance applyPWriterT :: (PartialSemigroup m w, Bind m) => Apply (PWriterT w m) where
  apply (PWriterT mf) (PWriterT ma) = PWriterT (join $ lift2 combine mf ma) where
    combine (Tuple w1 f) (Tuple w2 a) = pappend w1 w2 <#> \w -> Tuple w (f a)
instance applicativePWriterT :: (PartialMonoid m w, Bind m) => Applicative (PWriterT w m) where
  pure a = PWriterT $ purempty <#> \w -> Tuple w a
instance bindPWriterT :: (PartialSemigroup m w, Bind m) => Bind (PWriterT w m) where
  bind (PWriterT ma) f = PWriterT do
    Tuple w1 a <- ma
    Tuple w2 b <- case f a of PWriterT mb -> mb
    pappend w1 w2 <#> \w -> Tuple w b

type Gracefail o m = Tuple (Maybe o) m

-- Split a monoid `w` into a subsemigroup `o` that represents errors
-- (it should not contain the identity) and a subset `m` that represents a
-- partial monoid of success cases that may fail to combine.
class (Monoid w, ErrorSemigroup o m w) <= ErrorMonoid o m w | w -> o m where
  emempty :: w -> m
class (Semigroup w, Semigroup o) <= ErrorSemigroup o m w | w -> o m where
  split :: w -> These o m
  ocomb :: o -> w
  mcomb :: m -> w

instance errorSemigroupVoid :: ErrorSemigroup Void Void Void where
  split = absurd
  ocomb = absurd
  mcomb = absurd

instance errorSemigroupUnit :: ErrorSemigroup Void Unit Unit where
  split = That
  ocomb = absurd
  mcomb = identity
instance errorMonoidUnit :: ErrorMonoid Void Unit Unit where
  emempty = pure unit

foreign import data ErrorPart :: Type -> Type
mkErrorPart :: forall o m w. ErrorSemigroup o m w => o -> ErrorPart w
mkErrorPart = unsafeCoerce
unErrorPart :: forall o m w. ErrorSemigroup o m w => ErrorPart w -> o
unErrorPart = unsafeCoerce
upErrorPart :: forall o m w. ErrorSemigroup o m w => ErrorPart w -> w
upErrorPart = ocomb <<< unErrorPart
instance semigroupErrorPart :: ErrorSemigroup o m w => Semigroup (ErrorPart w) where
  append o1 o2 = mkErrorPart (unErrorPart o1 <> unErrorPart o2)
foreign import data StatePart :: Type -> Type
mkStatePart :: forall o m w. ErrorSemigroup o m w => m -> StatePart w
mkStatePart = unsafeCoerce
unStatePart :: forall o m w. ErrorSemigroup o m w => StatePart w -> m
unStatePart = unsafeCoerce
upStatePart :: forall o m w. ErrorSemigroup o m w => StatePart w -> w
upStatePart = mcomb <<< unStatePart
zeroState :: forall o m w. ErrorMonoid o m w => StatePart w
zeroState = mkStatePart (emempty (mempty :: w))

type GracefailParts w = Gracefail (ErrorPart w) (StatePart w)

eappend :: forall o m w. ErrorSemigroup o m w => StatePart w -> StatePart w -> These (ErrorPart w) (StatePart w)
eappend m1 m2 = bimap mkErrorPart mkStatePart (split (mcomb (unStatePart m1) <> mcomb (unStatePart m2) :: w))

emappend :: forall o m w. ErrorMonoid o m w => StatePart w -> StatePart w -> Gracefail (ErrorPart w) (StatePart w)
emappend m1 m2 = mollify zeroState (eappend m1 m2)

mollify :: forall o m. m -> These o m -> Gracefail o m
mollify m0 = case _ of
  This o -> Tuple (Just o) m0
  That m -> Tuple Nothing m
  Both o m -> Tuple (Just o) m

splitGrace :: forall o m w. ErrorMonoid o m w => w -> Gracefail (ErrorPart w) (StatePart w)
splitGrace = mollify zeroState <<< bimap mkErrorPart mkStatePart <<< split

data CrissCross o1 m1 o2 m2 = Criss o1 m2 | CrissCross o1 o2 | Cross m1 o2

errs :: forall o1 o2. Maybe o1 -> Maybe o2 -> Maybe (These o1 o2)
errs Nothing Nothing = Nothing
errs (Just o1) Nothing = Just (This o1)
errs Nothing (Just o2) = Just (That o2)
errs (Just o1) (Just o2) = Just (Both o1 o2)

instance errorSemigroupTuple ::
  (ErrorMonoid o1 m1 w1, ErrorMonoid o2 m2 w2) =>
  ErrorSemigroup (These o1 o2) (Tuple m1 m2) (Tuple w1 w2) where
    split (Tuple w1 w2) =
      let
        Tuple o1m m1 = mollify (emempty (mempty :: w1)) $ split w1
        Tuple o2m m2 = mollify (emempty (mempty :: w2)) $ split w2
      in case errs o1m o2m of
        Nothing -> That (Tuple m1 m2)
        Just o3m -> Both o3m (Tuple m1 m2)
    ocomb = case _ of
      This o1 -> Tuple (ocomb o1) mempty
      That o2 -> Tuple mempty (ocomb o2)
      Both o1 o2 -> Tuple (ocomb o1) (ocomb o2)
    mcomb (Tuple m1 m2) = Tuple (mcomb m1) (mcomb m2)
instance errorMonoidTuple ::
  (ErrorMonoid o1 m1 w1, ErrorMonoid o2 m2 w2) =>
  ErrorMonoid (These o1 o2) (Tuple m1 m2) (Tuple w1 w2) where
    emempty (Tuple w1 w2) = Tuple (emempty w1) (emempty w2)

instance errorSemigroupSemigroupMap :: (Ord k, ErrorSemigroup o m w) =>
  ErrorSemigroup (SemigroupMap k o) (SemigroupMap k m) (SemigroupMap k w) where
    split = map split >>> \(SemigroupMap together) ->
      Both (SemigroupMap (Map.mapMaybe theseLeft together)) (SemigroupMap (Map.mapMaybe theseRight together))
    ocomb = map ocomb
    mcomb = map mcomb
instance errorMonoidSemigroupMap :: (Ord k, ErrorSemigroup o m w) =>
  ErrorMonoid (SemigroupMap k o) (SemigroupMap k m) (SemigroupMap k w) where
    emempty = pure (SemigroupMap Map.empty)

instance errorSemigroupMaybe :: ErrorSemigroup o m w =>
  ErrorSemigroup o (Maybe m) (Maybe w) where
    split Nothing = That Nothing
    split (Just w) = Just <$> split w
    ocomb = Just <<< ocomb
    mcomb = map mcomb
instance errorMonoidMaybe :: ErrorSemigroup o m w =>
  ErrorMonoid o (Maybe m) (Maybe w) where
    emempty = pure Nothing





newtype Discrete a = Discrete a
instance partialSemigroupDiscrete :: (Applicative f, Plus f, Eq a) => PartialSemigroup f (Discrete a) where
  pappend (Discrete a1) (Discrete a2) = if a1 == a2 then pure (Discrete a1) else empty

instance errorSemigroupUntotalMaybe :: PartialSemigroup Maybe a => ErrorSemigroup Unit a (Untotal Maybe a) where
  split (Untotal Nothing) = This unit
  split (Untotal (Just a)) = That a
  ocomb (_ :: Unit) = Untotal Nothing
  mcomb a = Untotal (Just a)

instance errorSemigroupUntotalEither :: (Semigroup e, PartialSemigroup (EitherA e) a) => ErrorSemigroup e a (Untotal (EitherA e) a) where
  split (Untotal (EitherA (Left e))) = This e
  split (Untotal (EitherA (Right a))) = That a
  ocomb e = Untotal (EitherA (Left e))
  mcomb a = Untotal (EitherA (Right a))


newtype Tracked a = Tracked a
instance partialSemigroupUpDiscrete :: (PartialSemigroup Maybe a) => PartialSemigroup (EitherA (Inconsistency a)) (Tracked a) where
  pappend (Tracked a1) (Tracked a2) = case pappend a1 a2 of
    Nothing -> EitherA (Left (Inconsistent a1 a2))
    Just a3 -> EitherA (Right (Tracked a3))

data Inconsistency a = Inconsistent a a | Additional (Inconsistency a) a
derive instance functorInconsistency :: Functor (Inconsistency)
instance foldableInconsistency :: Foldable (Inconsistency) where
  foldMap f (Inconsistent a0 a1) = f a0 <> f a1
  foldMap f (Additional as a) = foldMap f as <> f a
  foldl f b (Inconsistent a0 a1) = f (f b a0) a1
  foldl f b (Additional as a) = f (foldl f b as) a
  foldr f b (Inconsistent a0 a1) = f a0 (f a1 b)
  foldr f b (Additional as a) = foldr f (f a b) as
instance foldable1Inconsistency :: Foldable1 (Inconsistency) where
  foldMap1 f (Inconsistent a0 a1) = f a0 <> f a1
  foldMap1 f (Additional as a) = foldMap1 f as <> f a
  foldr1 f = foldr1Default f
  foldl1 f = foldl1Default f
instance traversableInconsistency :: Traversable (Inconsistency) where
  traverse f (Inconsistent a0 a1) = Inconsistent <$> f a0 <*> f a1
  traverse f (Additional as a) = Additional <$> traverse f as <*> f a
  sequence (Inconsistent a0 a1) = Inconsistent <$> a0 <*> a1
  sequence (Additional as a) = Additional <$> sequence as <*> a
instance traversable1Inconsistency :: Traversable1 (Inconsistency) where
  traverse1 f (Inconsistent a0 a1) = Inconsistent <$> f a0 <*> f a1
  traverse1 f (Additional as a) = Additional <$> traverse1 f as <*> f a
  sequence1 (Inconsistent a0 a1) = Inconsistent <$> a0 <*> a1
  sequence1 (Additional as a) = Additional <$> sequence1 as <*> a

addInconsistency :: forall a. PartialSemigroup Maybe a => Inconsistency a -> a -> Inconsistency a
addInconsistency as' a' =
  let Tuple (Disj v) r = traverse merge as' in if v then r else Additional r a'
  where
    merge a0 = case pappend a0 a' of
      Just a1 -> Tuple (Disj true) a1
      Nothing -> pure a0

instance semigroupInconsistency :: (PartialSemigroup Maybe a) => Semigroup (Inconsistency a) where
  append as (Inconsistent a0 a1) =
    addInconsistency (addInconsistency as a0) a1
  append as0 (Additional as1 a) =
    addInconsistency (as0 <> as1) a

data Occurrences a = Occurrence a | Again (Occurrences a) a
derive instance functorOccurrences :: Functor (Occurrences)
instance foldableOccurrences :: Foldable (Occurrences) where
  foldMap f (Occurrence a0) = f a0
  foldMap f (Again as a) = foldMap f as <> f a
  foldl f b (Occurrence a0) = f b a0
  foldl f b (Again as a) = f (foldl f b as) a
  foldr f b (Occurrence a0) = f a0 b
  foldr f b (Again as a) = foldr f (f a b) as
instance foldable1Occurrences :: Foldable1 (Occurrences) where
  foldMap1 f (Occurrence a0) = f a0
  foldMap1 f (Again as a) = foldMap1 f as <> f a
  foldr1 f = foldr1Default f
  foldl1 f = foldl1Default f
instance traversableOccurrences :: Traversable (Occurrences) where
  traverse f (Occurrence a0) = Occurrence <$> f a0
  traverse f (Again as a) = Again <$> traverse f as <*> f a
  sequence (Occurrence a0) = Occurrence <$> a0
  sequence (Again as a) = Again <$> sequence as <*> a
instance traversable1Occurrences :: Traversable1 (Occurrences) where
  traverse1 f (Occurrence a0) = Occurrence <$> f a0
  traverse1 f (Again as a) = Again <$> traverse1 f as <*> f a
  sequence1 (Occurrence a0) = Occurrence <$> a0
  sequence1 (Again as a) = Again <$> sequence1 as <*> a

addOccurrences :: forall a. PartialSemigroup Maybe a => Occurrences a -> a -> Occurrences a
addOccurrences as' a' =
  let Tuple (Disj v) r = traverse merge as' in if v then r else Again r a'
  where
    merge a0 = case pappend a0 a' of
      Just a1 -> Tuple (Disj true) a1
      Nothing -> pure a0

instance semigroupOccurrences :: PartialSemigroup Maybe a => Semigroup (Occurrences a) where
  append as (Occurrence a0) =
    addOccurrences as a0
  append as0 (Again as1 a) =
    addOccurrences (as0 <> as1) a

isConsistent :: forall a. Occurrences a -> Either (Inconsistency a) a
isConsistent (Occurrence a) = Right a
isConsistent (Again as0 a0) = Left (mkInconsistent as0 a0)
  where
    mkInconsistent (Occurrence a1) = Inconsistent a1
    mkInconsistent (Again as a1) = Additional (mkInconsistent as a1)

type DiscreteWithInfo l a = Tuple (Total l) (Discrete a)
type OccurrencesWithInfo l a = Occurrences (DiscreteWithInfo l a)
type InconsistencyWithInfo l a = Inconsistency (DiscreteWithInfo l a)

type OccurrencesWithInfos l a = OccurrencesWithInfo (NonEmptyArray l) a
type InconsistencyWithInfos l a = InconsistencyWithInfo (NonEmptyArray l) a
type DiscreteWithInfos l a = DiscreteWithInfo (NonEmptyArray l) a

instance errorSemigroupOccurrences :: PartialSemigroup Maybe a => ErrorSemigroup (Inconsistency a) a (Occurrences a) where
  split = either This That <<< isConsistent
  ocomb (Inconsistent a0 a1) = Again (Occurrence a0) a1
  ocomb (Additional as a) = Again (ocomb as) a
  mcomb a = Occurrence a

data StateErroring w e a
  = Success (StatePart w) a
  | Error (These (ErrorPart w) (NonEmptyArray e)) (StatePart w) (Maybe a)
derive instance functorStateErroring :: Functor (StateErroring w e)
instance bifunctorStateErroring :: Bifunctor (StateErroring w) where
  bimap _ g (Success s a) = Success s (g a)
  bimap f g (Error es s ma) = Error (map (map f) es) s (map g ma)

acc :: forall o e. Semigroup o => Semigroup e =>
  These o e -> Maybe o -> These o e
acc = flip case _ of
  Nothing -> identity
  Just o2 -> case _ of
    This _ -> This o2
    That e1 -> Both o2 e1
    Both _ e1 -> Both o2 e1

eths :: forall o e. Semigroup o => Semigroup e =>
  These o e -> These o e -> These o e
eths = case _ of
  This o1 -> case _ of
    This o2 -> This (o1 <> o2)
    That e2 -> Both o1 e2
    Both o2 e2 -> Both (o1 <> o2) e2
  That e1 -> case _ of
    This o2 -> Both o2 e1
    That e2 -> That (e1 <> e2)
    Both o2 e2 -> Both o2 (e1 <> e2)
  Both o1 e1 -> case _ of
    This o2 -> Both (o1 <> o2) e1
    That e2 -> Both o1 (e1 <> e2)
    Both o2 e2 -> Both (o1 <> o2) (e1 <> e2)

exErrorPart :: forall o m w e. ErrorMonoid o m w => These (ErrorPart w) e -> w
exErrorPart = bifoldMap upErrorPart mempty

instance applyStateErroring :: (ErrorMonoid o m w) => Apply (StateErroring w e) where
  apply (Success m1 f) (Success m2 a) = case emappend m1 m2 of
    Tuple (Just o) m3 -> Error (This o) m3 (Just (f a))
    Tuple Nothing m3 -> Success m3 (f a)
  apply (Error e1 m1 mf) (Success m2 a) =
    case splitGrace (exErrorPart e1 <> upStatePart m1 <> upStatePart m2) of
      Tuple os m3 -> Error (acc e1 os) m3 (mf <#> (_ $ a))
  apply (Success m1 f) (Error e2 m2 ma) =
    case splitGrace (upStatePart m1 <> exErrorPart e2 <> upStatePart m2) of
      Tuple os m3 -> Error (acc e2 os) m3 ((f $ _) <$> ma)
  apply (Error e1 m1 mf) (Error e2 m2 ma) =
    case splitGrace (exErrorPart e1 <> upStatePart m1 <> exErrorPart e2 <> upStatePart m2) of
      Tuple os m3 -> Error (acc (eths e1 e2) os) m3 (mf <*> ma)

instance applicativeStateErroring :: (ErrorMonoid o m w) => Applicative (StateErroring w e) where
  pure = Success zeroState

instance bindStateErroring :: (ErrorMonoid o m w) => Bind (StateErroring w e) where
  bind (Success m1 a) f = case f a of
    Success m2 b -> case emappend m1 m2 of
      Tuple (Just o) m3 -> Error (This o) m3 (Just b)
      Tuple Nothing m3 -> Success m3 b
    Error e2 m2 mb ->
      case splitGrace (upStatePart m1 <> exErrorPart e2 <> upStatePart m2) of
        Tuple os m3 -> Error (acc e2 os) m3 mb
  bind (Error e1 m1 (Just a)) f = case f a of
    Success m2 b -> case splitGrace (exErrorPart e1 <> upStatePart m1 <> upStatePart m2) of
      Tuple os m3 -> Error (acc e1 os) m3 (Just b)
    Error e2 m2 mb -> case splitGrace (exErrorPart e1 <> upStatePart m1 <> exErrorPart e2 <> upStatePart m2) of
      Tuple os m3 -> Error (acc (eths e1 e2) os) m3 mb
  bind (Error e1 m1 Nothing) _ = Error e1 m1 Nothing

newtype LocStateErroring l w e a =
  LocStateErroring (l -> StateErroring w (Tuple l e) a)
derive instance functorLocStateErroring :: Functor (LocStateErroring l w e)

instance applyLocStateErroring :: (ErrorMonoid o m w) => Apply (LocStateErroring l w e) where
  apply (LocStateErroring mf) (LocStateErroring ma) = LocStateErroring \l ->
    mf l <*> ma l
instance applicativeLocStateErroring :: (ErrorMonoid o m w) => Applicative (LocStateErroring l w e) where
  pure = LocStateErroring <<< pure <<< pure
instance bindLocStateErroring :: (ErrorMonoid o m w) => Bind (LocStateErroring l w e) where
  bind (LocStateErroring ma) f = LocStateErroring \l ->
    ma l >>= \a -> case f a of LocStateErroring mb -> mb l

provideLoc :: forall l w e a. l -> LocStateErroring l w e a -> StateErroring w (Tuple l e) a
provideLoc l (LocStateErroring f) = f l

writeLocStateErroring :: forall l o m w e. ErrorMonoid o m w => m -> LocStateErroring l w e Unit
writeLocStateErroring m = LocStateErroring \_ ->
  Success (mkStatePart m) unit

throwLocStateErroring :: forall l o m w e a. ErrorMonoid o m w => e -> LocStateErroring l w e a
throwLocStateErroring e = LocStateErroring \l ->
  Error (That (pure (Tuple l e))) zeroState Nothing

localLocStateErroring :: forall l o m w e a. ErrorMonoid o m w => (l -> l) -> LocStateErroring l w e a -> LocStateErroring l w e a
localLocStateErroring ll (LocStateErroring f) = LocStateErroring \l0 -> f (ll l0)

askLocStateErroring :: forall l o m w e. ErrorMonoid o m w => LocStateErroring l w e l
askLocStateErroring = LocStateErroring \l -> Success zeroState l



escalate :: forall w e a. StateErroring w e a -> StateErroring w e a
escalate (Error es s _) = Error es s Nothing
escalate v = v

escalateR :: forall l w e a. LocStateErroring l w e a -> LocStateErroring l w e a
escalateR (LocStateErroring f) = LocStateErroring \l -> escalate (f l)


confirm :: forall w a b e. a -> StateErroring w e b -> StateErroring w e a
confirm a (Success s _) = Success s a
confirm a (Error es s _) = Error es s (Just a)

confirmW :: forall s w a b e. Monoid w => a -> W.WriterT w (StateErroring s e) b -> W.WriterT w (StateErroring s e) a
confirmW a = case _ of
  W.WriterT (Success s (Tuple _ accum)) ->
    W.WriterT (Success s (Tuple a accum))
  W.WriterT (Error es s mtaccum) ->
    W.WriterT (Error es s $ pure $ Tuple a $ foldMap extract mtaccum)

mconfirmW :: forall s w a e. Monoid w => Maybe a -> W.WriterT w (StateErroring s e) a -> W.WriterT w (StateErroring s e) a
mconfirmW = case _ of
  Nothing -> identity
  Just a -> confirmW a

confirmWR :: forall l s w a b e. Monoid w => a -> W.WriterT w (LocStateErroring l s e) b -> W.WriterT w (LocStateErroring l s e) a
confirmWR a (W.WriterT (LocStateErroring f)) = W.WriterT $ LocStateErroring \r ->
  case confirmW a (W.WriterT (f r)) of
    W.WriterT w -> w

mconfirmWR :: forall l s w a e. Monoid w => Maybe a -> W.WriterT w (LocStateErroring l s e) a -> W.WriterT w (LocStateErroring l s e) a
mconfirmWR = case _ of
  Nothing -> identity
  Just a -> confirmWR a

confirmR :: forall l s a b e. a -> LocStateErroring l s e b -> LocStateErroring l s e a
confirmR a (LocStateErroring f) = LocStateErroring \r -> confirm a (f r)

mconfirmR :: forall l s a e. Maybe a -> LocStateErroring l s e a -> LocStateErroring l s e a
mconfirmR = case _ of
  Nothing -> identity
  Just a -> confirmR a

--------------------------------------------------------------------------------

-- | Return the value inside the `Maybe` or throw the provide error.
note :: forall o m w e a. ErrorMonoid o m w => e -> Maybe a -> StateErroring w e a
note _ (Just a) = pure a
note e Nothing = erroring e

-- | Throw an error if the result is `Nothing`.
onFailure :: forall o m w e a. ErrorMonoid o m w => e -> StateErroring w e (Maybe a) -> StateErroring w e a
onFailure e c = c >>= note e

hush :: forall w e a. StateErroring w e a -> Maybe a
hush (Error _ _ ma) = ma
hush (Success _ a) = pure a

hush' :: forall w e a. StateErroring w e a -> Maybe a
hush' (Error _ _ _) = Nothing
hush' (Success _ a) = pure a

-- | Throw an error! No frills.
erroring :: forall o m w e a. ErrorMonoid o m w => e -> StateErroring w e a
erroring e = Error (pure (pure e)) zeroState empty

-- | Throw an error, but let the computation continue with a known result anyways.
erroringBut :: forall o m w e a. ErrorMonoid o m w => e -> a -> StateErroring w e a
erroringBut e a = Error (pure (pure e)) zeroState (pure a)

--------------------------------------------------------------------------------

-- | Lift from Errors to Feedback, ERrors to FeedbackR
liftW :: forall f a m. Functor f => Monoid m => f a -> W.WriterT m f a
liftW m = W.WriterT (Tuple <$> m <@> mempty)

unW :: forall f a m. Functor f => W.WriterT m f a -> f a
unW (W.WriterT m) = m <#> \(Tuple a _) -> a

hushW :: forall w m e a. W.WriterT m (StateErroring w e) a -> Maybe a
hushW (W.WriterT (Error _ _ ma)) = ma <#> \(Tuple a _) -> a
hushW (W.WriterT (Success _ (Tuple a _))) = pure a

hushW' :: forall w m e a. W.WriterT m (StateErroring w e) a -> Maybe a
hushW' (W.WriterT (Error _ _ _)) = Nothing
hushW' (W.WriterT (Success _ (Tuple a _))) = pure a

liftCL :: forall f g. Functor f => Applicative g => f ~> Compose f g
liftCL = Compose <<< map pure

liftCR :: forall f g. Applicative f => g ~> Compose f g
liftCR = Compose <<< pure

liftR :: forall l s e a. StateErroring s (Tuple l e) a -> LocStateErroring l s e a
liftR = LocStateErroring <<< pure

unR :: forall l s e a. LocStateErroring l s e a -> l -> StateErroring s (Tuple l e) a
unR (LocStateErroring f) l = f l



writeOther :: forall x o m w e. Monoid x => ErrorMonoid o m w => x -> StateErroring (Tuple (Total x) w) e Unit
writeOther x = Success (mkStatePart (Tuple (Total x) (emempty (mempty :: w)))) unit

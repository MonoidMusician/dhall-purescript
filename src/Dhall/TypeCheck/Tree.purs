module Dhall.TypeCheck.Tree where

import Prelude

import Control.Comonad (class Comonad, extract)
import Control.Comonad.Cofree (Cofree, buildCofree, deferCofree)
import Control.Comonad.Cofree as Cofree
import Control.Comonad.Env (EnvT(..), runEnvT)
import Data.Bifunctor (bimap)
import Data.Either (Either(..))
import Data.Functor.Compose (Compose(..))
import Data.Functor.Mu (Mu(..))
import Data.Functor.Product (Product(..))
import Data.Maybe (Maybe(..))
import Data.Newtype (un, unwrap)
import Data.Profunctor.Strong ((&&&))
import Data.Tuple (Tuple(..))
import Matryoshka (class Corecursive, class Recursive, ana, cata, embed, project, transCata)

-- This is a very peculiar kind of tree, ideal for typechecking.
-- What happens is that `f` represents the normal mode of branching: the layout
-- of the syntax. The next step is that `m` represents a functor of operations
-- to be applied to each AST, like typechecking and normalization. In this way,
-- catamorphic algorithms can walk the whole tree, running operations
-- arbitrarily deep in the tree without having to manually recurse. It also
-- helps to take advantage of sharing, since the operations can be lazy and
-- cached, so when one expression appears a lot its results only has to be
-- computed once.
type TwoD m f = Mu (Compose (Cofree m) f)
-- This is a kind of braiding of the regular syntax with the `TwoD` tree of
-- syntax and operations. Each node can either be a shared `TwoD` tree, or it
-- can descend through the syntax like usual. It turns out that this is the best
-- form for representing the results of algorithms, so they can exploit sharing
-- and generate new expressions that still have shareable children.
type HalfTwoD m f = Mu (Compose (Either (TwoD m f)) f)

-- Elaborate a tree like `Mu f` into `TwoD m f` using an algorithm like
-- `f (TwoD m f) -> m (Mu f)`. Operations are built lazily in the `Cofree`.
recursor2D ::
  forall t f m r.
    Recursive t f =>
    Corecursive r (Compose (Cofree m) f) =>
    Functor f =>
    Functor m =>
  -- e.g. (f (TwoD m f) -> m (Mu f)) -> Mu f -> TwoF m f
  (f r -> m t) -> t -> r
recursor2D f = go where
  go :: t -> r
  go = ana $ (<<<) Compose $ buildCofree $ (>>>) project $ do
    identity &&& \ft -> ft <#> go # f

-- Turn a `HalfTwoD m f` into `Mu f`, losing all sharing.
deshare :: forall m t f. Corecursive t f => Functor m => Functor f => HalfTwoD m f -> t
deshare = cata $ unwrap >>> case _ of
  Left r -> head2D r
  Right ft -> embed ft

-- Try to recover sharing at the top node.
wasShared :: forall m f. HalfTwoD m f -> Maybe (TwoD m f)
wasShared (In (Compose (Left r))) = Just r
wasShared _ = Nothing

-- Construct a shared value (cheap).
shared :: forall m f. TwoD m f -> HalfTwoD m f
shared r = In (Compose (Left r))

-- Construct an unshared value (expensive).
unshared :: forall m t f. Recursive t f => Functor f => t -> HalfTwoD m f
unshared = cata embedShared

-- Construct an unshared layer with (potentially) shared children.
embedShared :: forall m f. f (HalfTwoD m f) -> HalfTwoD m f
embedShared ft = In (Compose (Right ft))

-- Helpers for TwoD/HalfTwoD --

-- This is a fancy algorithm that generates `TwoD m f` from `HalfTwoD m f` while
-- threading context through. Certain assumptions are made about how context
-- works, namely that it stays constant through the operations `m`, while
-- the algorithm can control how it varies through the `f` dimension.
recursor2DSharingCtx ::
  forall t f m r ctx.
    Recursive t (Compose (Either r) f) =>
    Recursive r (Compose (Cofree m) f) =>
    Corecursive r (Compose (Cofree m) f) =>
    Functor f =>
    Functor m =>
  -- e.g. (ctx -> f (ctx -> TwoD m f) -> m (HalfTwoD m f)) ->
  --      HalfTwoD m f -> ctx -> TwoD m f
  (ctx -> f (ctx -> r) -> m t) -> t -> ctx -> r
recursor2DSharingCtx f = go where
  go :: t -> ctx -> r
  go t ctx = case unwrap (project t) of
    Left r -> r -- already a TwoD node
    Right ft -> embed (Compose (goCf ft ctx))
  goCf :: f t -> ctx -> Cofree m (f r)
  goCf ft ctx = deferCofree \_ ->
    let fr = go <$> ft in
    -- The head receives the current context, the tail can choose what context
    -- it propagates, based on the current one.
    Tuple (fr <@> ctx) $ (f ctx fr :: m t) <#> \t ->
      case unwrap (project t) of
        -- Assume that the passed through node already has its proper context
        -- (after all, there is nothing we can do anymore)
        Left r -> unwrap (project r)
        -- Assume that the next layer of *operations* starts with the same
        -- context (again, not much we can do)
        Right ft' -> goCf ft' ctx

-- Return the syntax tree at the head, running no operations.
head2D ::
  forall t f w r. Comonad w =>
    Recursive r (Compose w f) =>
    Corecursive t f =>
  -- e.g. TwoD m f -> Mu f
  r -> t
head2D = transCata $ extract <<< un Compose

-- Get the functor of operations at the head.
step2D ::
  forall f m r. Functor m =>
    Recursive r (Compose (Cofree m) f) =>
    Corecursive r (Compose (Cofree m) f) =>
  r -> m r
step2D = project >>> un Compose >>> Cofree.tail >>> map (Compose >>> embed)

dubstep2D ::
  forall f m r. Bind m =>
    Recursive r (Compose (Cofree m) f) =>
    Corecursive r (Compose (Cofree m) f) =>
  r -> m r
dubstep2D = step2D <=< step2D

headAndSpine ::
  forall t a f.
    Corecursive t f =>
  Cofree f a -> Tuple a t
headAndSpine = Cofree.head &&& transCata (runEnvT >>> extract)

unEnvT :: forall e f a. EnvT e f a -> f a
unEnvT (EnvT (Tuple _ fa)) = fa

env :: forall e f a. EnvT e f a -> e
env (EnvT (Tuple e _)) = e

mapEnv :: forall e e' f a. (e -> e') -> EnvT e f a -> EnvT e' f a
mapEnv f (EnvT (Tuple e fa)) = EnvT (Tuple (f e) fa)

bitransProduct :: forall f g a h l b. (f a -> h b) -> (g a -> l b) -> Product f g a -> Product h l b
bitransProduct natF natG (Product e) = Product (bimap natF natG e)

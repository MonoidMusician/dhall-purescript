module Dhall.Core.Zippers.Recursive where

import Prelude

import Control.Comonad (extract)
import Data.Either (Either(..), either)
import Data.Functor.Mu (Mu)
import Data.Lazy (Lazy)
import Data.Lens (Iso', Prism', Traversal', firstOf, iso, prism')
import Data.List (List(..), (:))
import Data.Maybe (Maybe)
import Data.Profunctor.Strong ((&&&))
import Data.TraversableWithIndex (class TraversableWithIndex)
import Data.Tuple (Tuple(..))
import Dhall.Core.Zippers (class Container, class ContainerI, _ix, downZF, ixF, upZF, (:<-:))
import Matryoshka (class Corecursive, class Recursive, embed, project)

type Indices i = List (Lazy i)
type ParentCtxs f x = List (Lazy (f x))
data ZRec f x = ZRec x (ParentCtxs f x)
type ZRecMu f = ZRec f (Mu f)
infix 1 ZRec as :<<~:

atTop :: forall f x. x -> ZRec f x
atTop focus = ZRec focus Nil

ixZRec :: forall i f x. ContainerI i f => ZRec f x -> Indices i
ixZRec (_ :<<~: context) = ixParentContexts context

ixParentContexts :: forall i f x. ContainerI i f => ParentCtxs f x -> Indices i
ixParentContexts context = context <#> map ixF

previewIndicesZRec ::
  forall i f f' t.
    Recursive t f =>
    Container i f f' =>
  Indices i -> ZRec f' t -> Maybe (ZRec f' t)
previewIndicesZRec Nil = pure
previewIndicesZRec (i : is) = downZRec
  >>> firstOf (_ix (extract i))
  >=> previewIndicesZRec is

_recurse :: forall t f. Recursive t f => Corecursive t f => Iso' t (f t)
_recurse = iso project embed

_ixes ::
  forall i f t.
    Recursive t f =>
    Corecursive t f =>
    TraversableWithIndex i f =>
    Eq i =>
  Indices i -> Traversal' t t
_ixes Nil = identity
_ixes (i : is) = _recurse <<< _ix (extract i) <<< _ixes is

_ixes_wholeZRec ::
  forall i f f' t.
    Container i f f' =>
    Recursive t f =>
    Corecursive t f =>
  Prism' (Tuple (Indices i) t) (ZRec f' t)
_ixes_wholeZRec = prism' (ixZRec &&& topZRec)
  \(Tuple is f) -> previewIndicesZRec is (atTop f)

downZRec ::
  forall t f f' i.
    Recursive t f =>
    Container i f f' =>
  ZRec f' t -> f (ZRec f' t)
downZRec (focus :<<~: context) = downZF (project focus) <#>
  case _ of
    fc :<-: cx ->
       fc :<<~: cx : context

upZRec ::
  forall t f f' i.
    Corecursive t f =>
    Container i f f' =>
  ZRec f' t -> Either t (ZRec f' t)
upZRec (focus :<<~: Nil) = Left focus
upZRec (focus :<<~: cx : context) = Right $
  embed (upZF (focus :<-: cx)) :<<~: context

topZRec ::
  forall t f f' i.
    Corecursive t f =>
    Container i f f' =>
  ZRec f' t -> t
topZRec z = either identity topZRec (upZRec z)

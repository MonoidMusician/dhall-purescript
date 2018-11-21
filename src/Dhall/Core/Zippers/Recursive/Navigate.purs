module Dhall.Core.Zippers.Recursive.Navigate where

import Dhall.Core.Zippers.Recursive (ZRec(..), downZRec, upZRec, (:<<~:))
import Prelude

import Control.Alternative (class Alternative, empty)
import Control.Comonad (extract)
import Data.Either (either)
import Data.List (List(..), (:))
import Data.Maybe (Maybe)
import Data.Maybe.First (First(..))
import Data.Maybe.Last (Last(..))
import Data.Newtype (unwrap)
import Dhall.Core.Zippers (class Container, ixF, upZF, (:<-:))
import Dhall.Core.Zippers.Navigate (childrenWith, pureFor)
import Matryoshka (class Corecursive, class Recursive, embed)

top :: forall f t. t -> ZRec f t
top focus = ZRec focus Nil

up ::
  forall t f f' i.
    Corecursive t f =>
    Container i f f' =>
  ZRec f' t -> ZRec f' t
up = upZRec >>> either top identity

downWith ::
  forall t f f' i pos x y.
    Recursive t f =>
    Container i f f' =>
    Alternative pos =>
  (x -> pos y) ->
  (i -> Boolean) ->
  ZRec f' t -> pos (ZRec f' t)
downWith typeHint matches = downZRec >>> childrenWith typeHint matches

left ::
  forall t f f' i.
    Recursive t f =>
    Corecursive t f =>
    Container i f f' =>
  ZRec f' t -> Maybe (ZRec f' t)
left (_ :<<~: Nil) = empty
left (focus :<<~: cx : context) = unwrap
  let i = ixF (extract cx) in
  downWith (pureFor Last) (_ < i)
    (embed (upZF (focus :<-: cx)) :<<~: context)

right ::
  forall t f f' i.
    Recursive t f =>
    Corecursive t f =>
    Container i f f' =>
  ZRec f' t -> Maybe (ZRec f' t)
right (_ :<<~: Nil) = empty
right (focus :<<~: cx : context) = unwrap
  let i = ixF (extract cx) in
  downWith (pureFor First) (_ > i)
    (embed (upZF (focus :<-: cx)) :<<~: context)

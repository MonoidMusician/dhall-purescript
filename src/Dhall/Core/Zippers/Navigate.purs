module Dhall.Core.Zippers.Navigate where

import Dhall.Core.Zippers (class Container, ZF4, downZF4, ixZF4, upZF4)
import Prelude

import Control.Alternative (class Alternative)
import Data.HeytingAlgebra (tt)
import Data.Lens (elementsOf, foldMapOf)
import Data.Lens.Indexed (itraversed, unIndex)
import Data.Maybe.First (First(..))
import Data.Maybe.Last (Last(..))
import Data.Monoid.Alternate (Alternate(..))
import Data.TraversableWithIndex (class TraversableWithIndex)

pureFor :: forall x y f a. Applicative f => (x -> f y) -> a -> f a
pureFor _ = pure

childrenWith ::
  forall i f a pos x y.
    TraversableWithIndex i f =>
    Alternative pos =>
  (x -> pos y) ->
  (i -> Boolean) ->
  f a -> pos a
childrenWith _ matches z =
  let relevant = elementsOf itraversed matches in
  case foldMapOf (unIndex relevant) pure z of
    Alternate r -> r

firstChild :: forall i f f' a. Container i f f' =>
  f a -> First (ZF4 f f' a)
firstChild = childrenWith First tt <<< downZF4

lastChild :: forall i f f' a. Container i f f' =>
  f a -> Last (ZF4 f f' a)
lastChild = childrenWith Last tt <<< downZF4

nextChild :: forall i f f' a. Container i f f' =>
  ZF4 f f' a -> First (ZF4 f f' a)
nextChild z = let i = ixZF4 z in
  childrenWith First (_ > i) (downZF4 (upZF4 z))

prevChild :: forall i f f' a. Container i f f' =>
  ZF4 f f' a -> Last (ZF4 f f' a)
prevChild z = let i = ixZF4 z in
  childrenWith Last (_ < i) (downZF4 (upZF4 z))

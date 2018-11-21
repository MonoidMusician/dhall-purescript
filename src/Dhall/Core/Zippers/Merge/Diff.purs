module Dhall.Core.Zippers.Merge.Diff where

import Data.Foldable (class Foldable, all)
import Data.Functor (class Functor, (<$>))
import Data.Maybe (Maybe(..))
import Dhall.Core.AST (Pair(..))
import Dhall.Core.Zippers.Merge (class Merge, mergeWith)
import Matryoshka (class Corecursive, class Recursive, embed, project)

data Diff f a = Similar (f (Diff f a)) | Different a
derive instance functorDiff :: Functor f => Functor (Diff f)

-- areSame (diff t1 t2) == (t1 == t2)
areSame :: forall f a. Foldable f => Diff f a -> Boolean
areSame (Similar shape) = all areSame shape
areSame (Different _) = false

diff ::
  forall t f.
    Recursive t f =>
    Merge f =>
  t -> t -> Diff f (Pair t)
diff t1 t2 =
  case mergeWith diff (project t1) (project t2) of
    Nothing -> Different (Pair t1 t2)
    Just shape -> Similar shape

-- before (diff t1 t2) == t1
before :: forall f t. Corecursive t f => Diff f (Pair t) -> t
before (Similar shape) = embed (before <$> shape)
before (Different (Pair t _)) = t

-- after (diff t1 t2) == t2
after :: forall f t. Corecursive t f => Diff f (Pair t) -> t
after (Similar shape) = embed (after <$> shape)
after (Different (Pair _ t)) = t

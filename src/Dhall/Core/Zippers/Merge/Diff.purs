module Dhall.Core.Zippers.Merge.Diff where

import Data.Functor ((<$>))
import Data.Foldable (class Foldable, all)
import Data.Maybe (Maybe(..))
import Dhall.Core.Zippers.Merge (class Merge, mergeWith)
import Matryoshka (class Corecursive, class Recursive, embed, project)

data DiffMu f t = Similar (f (DiffMu f t)) | Different t t

-- areSame (diff t1 t2) == (t1 == t2)
areSame :: forall f t. Foldable f => DiffMu f t -> Boolean
areSame (Similar shape) = all areSame shape
areSame (Different _ _) = false

diff ::
  forall t f.
    Recursive t f =>
    Merge f =>
  t -> t -> DiffMu f t
diff t1 t2 =
  case mergeWith diff (project t1) (project t2) of
    Nothing -> Different t1 t2
    Just shape -> Similar shape

-- before (diff t1 t2) == t1
before :: forall f t. Corecursive t f => DiffMu f t -> t
before (Similar shape) = embed (before <$> shape)
before (Different t _) = t

-- after (diff t1 t2) == t2
after :: forall f t. Corecursive t f => DiffMu f t -> t
after (Similar shape) = embed (after <$> shape)
after (Different _ t) = t

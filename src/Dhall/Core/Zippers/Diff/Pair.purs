module Dhall.Core.Zippers.Diff.Pair where

import Dhall.Core.AST (Pair(..))
import Dhall.Core.Zippers.Diff (Diff, diffWith, recover)
import Dhall.Core.Zippers.Merge (class Merge)
import Matryoshka (class Corecursive, class Recursive)

-- I dislike using a custom Pair type for generic operations,
-- so this is its own file
diff ::
  forall t f.
    Recursive t f =>
    Merge f =>
  t -> t -> Diff f (Pair t)
diff = diffWith Pair

-- before (diff t1 t2) == t1
before :: forall f t. Corecursive t f => Diff f (Pair t) -> t
before = recover \(Pair t _) -> t

-- after (diff t1 t2) == t2
after :: forall f t. Corecursive t f => Diff f (Pair t) -> t
after = recover \(Pair _ t) -> t

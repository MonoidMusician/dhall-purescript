module Dhall.Interactive.Types where


import Prelude

import Data.Either (Either)
import Data.Map (Map)
import Data.Set (Set)
import Data.Variant (Variant)
import Dhall.Core.AST (Expr)
import Dhall.Map (InsOrdStrMap)

data Import = Import String
derive instance eqImport :: Eq Import
instance showImport :: Show Import where
  show (Import s) = "(Import " <> show s <> ")"
data Hole = Hole
derive instance eqHole :: Eq Hole
instance showHole :: Show Hole where
  show Hole = "Hole"

-- FIXME
type InteractiveExpr (v :: # Type) = Expr InsOrdStrMap {-(Set (Variant v))-} (Either Import Hole)
type Annotations =
  ( collapsed :: Boolean
  )
type Annotation v = Set (Variant v)

type DB = Map Import (InteractiveExpr Annotations)

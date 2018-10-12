module Dhall.Interactive.Types where


import Prelude

import Data.Either (Either)
import Data.Map (Map)
import Data.Set (Set)
import Data.Variant (Variant)
import Dhall.Core.AST (Expr)
import Dhall.Core.StrMapIsh (InsOrdStrMap)

data Import = Import String
derive instance eqImport :: Eq Import
instance showImport :: Show Import where
  show (Import s) = "(Import " <> show s <> ")"
data Hole = Hole
derive instance eqHole :: Eq Hole
instance showHole :: Show Hole where
  show Hole = "Hole"

type InteractiveExpr v = Expr InsOrdStrMap (Set (Variant v)) (Either Import Hole)
type Annotation =
  ( collapsed :: Boolean
  )

type DB = Map Import (InteractiveExpr Annotation)

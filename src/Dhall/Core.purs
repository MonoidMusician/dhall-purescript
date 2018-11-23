module Dhall.Core ( reservedIdentifiers, module Exports ) where


import Data.Set (Set)
import Data.Set as Set
import Dhall.Core.AST
  ( _S, S_
  , AllTheThings
  , BuiltinBinOps
  , BuiltinFuncs
  , BuiltinOps
  , BuiltinTypes
  , BuiltinTypes2
  , Const(..)
  , Expr(..)
  , ExprRow
  , FunctorThings
  , LetF(..)
  , Literals
  , Literals2
  , MergeF(..)
  , Pair(..)
  , SimpleThings
  , Syntax
  , Terminals
  , TextLitF(..)
  , Triplet(..)
  , Var(..)
  , _Expr
  , _ExprF
  ) as Exports
import Dhall.Core.Imports
  ( Directory(..)
  , File(..)
  , FilePrefix(..)
  , Import(..)
  , ImportHashed(..)
  , ImportMode(..)
  , ImportType(..)
  , prettyDirectory
  , prettyFile
  , prettyFilePrefix
  , prettyImport
  , prettyImportHashed
  , prettyImportType
  ) as Exports
import Dhall.Normalize
  ( Normalizer(..)
  , boundedType
  , isNormalized
  , isNormalizedWith
  , judgmentallyEqual
  , normalize
  , normalizeWith
  ) as Exports
import Dhall.Normalize.Apps
  ( Apps(..)
  , _NoApp
  , apps
  , noapp
  , noapplit
  , (~)
  ) as Exports
import Dhall.Variables
  ( alphaNormalize
  , freeIn
  , rename
  , shift
  , shiftSubstShift
  , shiftSubstShift0
  , subst
  ) as Exports

-- | The set of reserved identifiers for the Dhall language
reservedIdentifiers :: Set String
reservedIdentifiers = Set.fromFoldable
  [ "let"
  , "in"
  , "Type"
  , "Kind"
  , "forall"
  , "Bool"
  , "True"
  , "False"
  , "merge"
  , "if"
  , "then"
  , "else"
  , "as"
  , "using"
  , "constructors"
  , "Natural"
  , "Natural/fold"
  , "Natural/build"
  , "Natural/isZero"
  , "Natural/even"
  , "Natural/odd"
  , "Natural/toInteger"
  , "Natural/show"
  , "Integer"
  , "Integer/show"
  , "Integer/toDouble"
  , "Double"
  , "Double/show"
  , "Text"
  , "List"
  , "List/build"
  , "List/fold"
  , "List/length"
  , "List/head"
  , "List/last"
  , "List/indexed"
  , "List/reverse"
  , "Optional"
  , "Optional/build"
  , "Optional/fold"
  ]

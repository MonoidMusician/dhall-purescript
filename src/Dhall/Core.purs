module Dhall.Core ( reservedIdentifiers, module Exports ) where


import Data.Set (Set)
import Data.Set as Set
import Dhall.Core.AST
  ( AllTheThings
  , AllTheThings'
  , AllTheThingsI
  , BinOpPrism
  , BindingBody(..)
  , BuiltinBinOps
  , BuiltinBinOps'
  , BuiltinBinOpsI
  , BuiltinFuncs
  , BuiltinFuncs'
  , BuiltinFuncsI
  , BuiltinOps
  , BuiltinOps'
  , BuiltinOpsI
  , BuiltinTypes
  , BuiltinTypes'
  , BuiltinTypes2
  , BuiltinTypes2'
  , BuiltinTypes2I
  , BuiltinTypesI
  , CONST
  , Const(..)
  , Double(..)
  , Expr(..)
  , Expr'
  , ExprFPrism
  , ExprI
  , ExprLayer
  , ExprLayerF
  , ExprLayerF'
  , ExprLayerFI
  , ExprLayerRow
  , ExprLayerRow'
  , ExprLayerRowI
  , ExprPrism
  , ExprRow
  , ExprRow'
  , ExprRowI
  , ExprRowVF(..)
  , ExprRowVF'(..)
  , ExprRowVFI(..)
  , FunctorThings
  , FunctorThings'
  , FunctorThingsI
  , ImportSyntax
  , ImportSyntax'
  , ImportSyntaxI
  , Integer(..)
  , LetF(..)
  , Literals
  , Literals'
  , Literals2
  , Literals2'
  , Literals2I
  , LiteralsI
  , MergeF(..)
  , Natural(..)
  , Pair(..)
  , S_
  , SimpleExpr
  , SimplePrism
  , SimpleThings
  , SimpleThings'
  , SimpleThingsI
  , Syntax
  , Syntax'
  , SyntaxI
  , TextLitF(..)
  , Three(..)
  , Triplet(..)
  , UNIT
  , Var(..)
  , Variable
  , Variable'
  , VariableI
  , _Annot
  , _App
  , _BinOp
  , _BinOpPrism
  , _Bool
  , _BoolAnd
  , _BoolEQ
  , _BoolIf
  , _BoolLit
  , _BoolLit_False
  , _BoolLit_True
  , _BoolNE
  , _BoolOr
  , _Combine
  , _CombineTypes
  , _Const
  , _Double
  , _DoubleLit
  , _DoubleShow
  , _E
  , _Embed
  , _Expr
  , _ExprF
  , _ExprFPrism
  , _ExprPrism
  , _Field
  , _Hashed
  , _ImportAlt
  , _Integer
  , _IntegerClamp
  , _IntegerLit
  , _IntegerNegate
  , _IntegerShow
  , _IntegerToDouble
  , _Lam
  , _Let
  , _List
  , _ListAppend
  , _ListBuild
  , _ListFold
  , _ListHead
  , _ListIndexed
  , _ListLast
  , _ListLength
  , _ListLit
  , _ListReverse
  , _Merge
  , _Natural
  , _NaturalBuild
  , _NaturalEven
  , _NaturalFold
  , _NaturalIsZero
  , _NaturalLit
  , _NaturalLit_0
  , _NaturalLit_1
  , _NaturalOdd
  , _NaturalPlus
  , _NaturalShow
  , _NaturalSubtract
  , _NaturalTimes
  , _NaturalToInteger
  , _None
  , _Optional
  , _Pi
  , _Prefer
  , _Project
  , _Record
  , _RecordCompletion
  , _RecordLit
  , _RecordLit_empty
  , _Record_empty
  , _S
  , _Some
  , _Text
  , _TextAppend
  , _TextLit
  , _TextLit_empty
  , _TextLit_single
  , _TextReplace
  , _TextShow
  , _ToMap
  , _Union
  , _Union_empty
  , _UsingHeaders
  , _Var
  , _With
  , conv
  , convTo
  , embedW
  , hoistExpr
  , mkAnnot
  , mkApp
  , mkArrow
  , mkBinOp
  , mkBool
  , mkBoolAnd
  , mkBoolEQ
  , mkBoolIf
  , mkBoolLit
  , mkBoolNE
  , mkBoolOr
  , mkCombine
  , mkCombineTypes
  , mkConst
  , mkDouble
  , mkDoubleLit
  , mkDoubleShow
  , mkEmbed
  , mkExpr
  , mkExprF
  , mkField
  , mkForall
  , mkHashed
  , mkImportAlt
  , mkInteger
  , mkIntegerClamp
  , mkIntegerLit
  , mkIntegerNegate
  , mkIntegerShow
  , mkIntegerToDouble
  , mkKind
  , mkLam
  , mkLet
  , mkList
  , mkListAppend
  , mkListBuild
  , mkListFold
  , mkListHead
  , mkListIndexed
  , mkListLast
  , mkListLength
  , mkListLit
  , mkListReverse
  , mkMerge
  , mkNatural
  , mkNaturalBuild
  , mkNaturalEven
  , mkNaturalFold
  , mkNaturalIsZero
  , mkNaturalLit
  , mkNaturalOdd
  , mkNaturalPlus
  , mkNaturalShow
  , mkNaturalSubtract
  , mkNaturalTimes
  , mkNaturalToInteger
  , mkNone
  , mkOptional
  , mkPi
  , mkPrefer
  , mkProject
  , mkRecord
  , mkRecordCompletion
  , mkRecordLit
  , mkSome
  , mkSort
  , mkText
  , mkTextAppend
  , mkTextLit
  , mkTextLit'
  , mkTextReplace
  , mkTextShow
  , mkToMap
  , mkType
  , mkUnion
  , mkUsingHeaders
  , mkVar
  , mkWith
  , projectW
  , rehydrate
  , rewriteBottomUp
  , rewriteBottomUpA
  , rewriteTopDown
  , rewriteTopDownA
  , unordered
  , vfCase
  , vfEq1Case
  , vfEqCase
  , vfOrd1Case
  , vfOrdCase
  ) as Exports
import Dhall.Core.Imports
  ( Directory(..)
  , File(..)
  , FilePrefix(..)
  , Header
  , Headers
  , Import(..)
  , ImportMode(..)
  , ImportType(..)
  , Scheme(..)
  , URL(..)
  , addHeaders
  , canonicalizeDirectory
  , canonicalizeFile
  , canonicalizeImport
  , canonicalizeImportType
  , getHeader
  , getHeaders
  , isLocal
  , mkDirectory
  , mkFile
  , parent
  , parseDirectory
  , parseFile
  , parseFilePrefix
  , parseImportType
  , parseScheme
  , parseURL
  , prettyDirectory
  , prettyFile
  , prettyFilePrefix
  , prettyImport
  , prettyImportType
  , prettyURL
  , unDirectory
  ) as Exports
import Dhall.Normalize
  ( Normalizer
  , GNormalizerF(..)
  , boundedTypeG
  , isNormalized
  , isNormalizedWith
  , judgmentallyEqual
  , normalize
  , normalizeWith
  ) as Exports
import Dhall.Normalize.Apps
  ( Apps
  , AppsF(..)
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
import Dhall.Map
  ( InsOrdMap(..)
  , InsOrdStrMap
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

module Dhall.Parser where

import Prelude

import Control.Monad.Except (runExcept)
import Data.Array (any)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Function (on)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Variant (FProxy, SProxy, VariantF)
import Data.Functor.Variant as VariantF
import Data.HeytingAlgebra (ff, tt)
import Data.Lens (preview)
import Data.List (List)
import Data.Maybe (Maybe(..))
import Data.Monoid.Disj (Disj(..))
import Data.Newtype (unwrap)
import Data.Nullable (Nullable)
import Data.Nullable as Nullable
import Data.Symbol (class IsSymbol)
import Data.Tuple (Tuple(..))
import Dhall.Core (S_, _s)
import Dhall.Core.AST (Const(..), Expr, ExprLayerRow, TextLitF(..), Var(..), projectW)
import Dhall.Core.AST as AST
import Dhall.Core.Imports (Directory, File(..), FilePrefix(..), Import(..), ImportHashed(..), ImportMode(..), ImportType(..), Scheme(..), URL(..))
import Dhall.Core.StrMapIsh as IOSM
import Dhall.Parser.Prioritize (POrdering)
import Dhall.Parser.Prioritize as Prioritize
import Foreign (Foreign)
import Foreign as Foreign
import Partial.Unsafe (unsafeCrashWith)
import Prim.Row as Row
import Unsafe.Coerce (unsafeCoerce)

type ParseExpr = Expr IOSM.InsOrdStrMap Import

parse :: String -> Maybe ParseExpr
parse s = case Nullable.toMaybe (parseImpl s) of
  Just [r] -> Just (decodeFAST r)
  _ -> Nothing

foreign import parseImpl :: String -> Nullable (Array (FAST Foreign))

newtype FAST a = FAST
  { "type" :: String
  , "value" :: Array a
  }
fromForeign :: Foreign -> FAST Foreign
fromForeign = unsafeCoerce

decodeS :: Foreign -> String
decodeS = unsafeCoerce

decodeN :: forall r. (Foreign -> r) -> Foreign -> Maybe r
decodeN decoder = map decoder
  <<< Nullable.toMaybe
  <<< (unsafeCoerce :: Foreign -> Nullable Foreign)

decodeA :: forall r. (Foreign -> r) -> Foreign -> Array r
decodeA decoder = map decoder
  <<< (unsafeCoerce :: Foreign -> Array Foreign)

decodeFAST :: FAST Foreign -> ParseExpr
decodeFAST (FAST r) =
  let
    decodeF :: Foreign -> ParseExpr
    decodeF = unsafeCoerce decodeFAST
  in case r."type", r."value" of
    "Type", _ -> AST.mkConst Type
    "Kind", _ -> AST.mkConst Kind
    "True", _ -> AST.mkBoolLit true
    "False", _ -> AST.mkBoolLit false
    "Bool", _ -> AST.mkBool
    "Natural", _ -> AST.mkNatural
    "Integer", _ -> AST.mkInteger
    "Double", _ -> AST.mkDouble
    "Text", _ -> AST.mkText
    "List", _ -> AST.mkList
    "Optional", _ -> AST.mkOptional
    "Natural/fold", _ -> AST.mkNaturalFold
    "Natural/build", _ -> AST.mkNaturalBuild
    "Natural/isZero", _ -> AST.mkNaturalIsZero
    "Natural/even", _ -> AST.mkNaturalEven
    "Natural/odd", _ -> AST.mkNaturalOdd
    "Natural/toInteger", _ -> AST.mkNaturalToInteger
    "Natural/show", _ -> AST.mkNaturalShow
    "Integer/show", _ -> AST.mkIntegerShow
    "Integer/toDouble", _ -> AST.mkIntegerToDouble
    "Double/show", _ -> AST.mkDoubleShow
    "List/build", _ -> AST.mkListBuild
    "List/fold", _ -> AST.mkListFold
    "List/length", _ -> AST.mkListLength
    "List/head", _ -> AST.mkListHead
    "List/last", _ -> AST.mkListLast
    "List/indexed", _ -> AST.mkListIndexed
    "List/reverse", _ -> AST.mkListReverse
    "Optional/fold", _ -> AST.mkOptionalFold
    "Optional/build", _ -> AST.mkOptionalBuild
    "BoolAnd", [a, b] -> AST.mkBoolAnd (decodeF a) (decodeF b)
    "BoolOr", [a, b] -> AST.mkBoolOr (decodeF a) (decodeF b)
    "BoolEQ", [a, b] -> AST.mkBoolEQ (decodeF a) (decodeF b)
    "BoolNE", [a, b] -> AST.mkBoolNE (decodeF a) (decodeF b)
    "NaturalPlus", [a, b] -> AST.mkNaturalPlus (decodeF a) (decodeF b)
    "NaturalTimes", [a, b] -> AST.mkNaturalTimes (decodeF a) (decodeF b)
    "TextAppend", [a, b] -> AST.mkTextAppend (decodeF a) (decodeF b)
    "ListAppend", [a, b] -> AST.mkListAppend (decodeF a) (decodeF b)
    "Combine", [a, b] -> AST.mkCombine (decodeF a) (decodeF b)
    "CombineTypes", [a, b] -> AST.mkCombineTypes (decodeF a) (decodeF b)
    "Prefer", [a, b] -> AST.mkPrefer (decodeF a) (decodeF b)
    "ImportAlt", [a, b] -> AST.mkImportAlt (decodeF a) (decodeF b)
    "App", [a, b] -> AST.mkApp (decodeF a) (decodeF b)
    "BoolIf", [a, b, c] -> AST.mkBoolIf (decodeF a) (decodeF b) (decodeF c)
    "Field", [a, b] -> AST.mkField (decodeF a) (decodeS b)
    "Project", [a, b] -> AST.mkProject (decodeF a) (IOSM.fromFoldable (Tuple <$> decodeA decodeS b <@> unit))
    "Merge", [a, b, c] -> AST.mkMerge (decodeF a) (decodeF b) (decodeN decodeF c)
    "Constructors", [a] -> AST.mkConstructors (decodeF a)
    "Lam", [a, b, c] -> AST.mkLam (decodeS a) (decodeF b) (decodeF c)
    "Pi", [a, b, c] -> AST.mkPi (decodeS a) (decodeF b) (decodeF c)
    "Let", [a, b, c, d] -> AST.mkLet (decodeS a) (decodeN decodeF b) (decodeF c) (decodeF d)
    "Annot", [a, b] -> AST.mkAnnot (decodeF a) (decodeF b)
    "Var", [a, b] -> AST.mkVar (V (decodeS a) (unsafeCoerce b))
    "NaturalLit", [a] -> AST.mkNaturalLit (unsafeCoerce a)
    "IntegerLit", [a] -> AST.mkIntegerLit (unsafeCoerce a)
    "DoubleLit", [a] -> AST.mkDoubleLit (unsafeCoerce a)
    "TextLit", vs -> AST.mkTextLit (decodeTextLit vs)
    "OptionalLit", [a, b] -> AST.mkOptionalLit (decodeF b) (Array.head (decodeA decodeF a))
    "Some", [a] -> AST.mkSome (decodeF a)
    "None", _ -> AST.mkNone
    "ListLit", [a, b] -> AST.mkListLit (decodeN decodeF b) (decodeA decodeF a)
    "Record", vs -> AST.mkRecord (decodeLabelled vs)
    "RecordLit", vs -> AST.mkRecordLit (decodeLabelled vs)
    "Union", vs -> AST.mkUnion (decodeLabelled vs)
    "UnionLit", _
      | Just { head, tail: vs } <- Array.uncons r."value"
      , [label, value] <- decodeA identity head ->
        AST.mkUnionLit (decodeS label) (decodeF value) (decodeLabelled vs)

    "Import", [a, b] -> pure $ Import
      { importHashed: decodeImportHashed (fromForeign a)
      , importMode: if Foreign.isNull b then Code else RawText
      }
    _, _ -> unsafeCrashWith "Unrecognized Expr"

decodeTextLit :: Array Foreign -> TextLitF ParseExpr
decodeTextLit = Array.foldr f (TextLit "") where
  f next result = case runExcept (Foreign.readString next) of
    Left _ -> TextInterp "" (decodeFAST (fromForeign next)) result
    Right s' ->
      case result of
        TextLit s -> TextLit (s' <> s)
        TextInterp s a t -> TextInterp (s' <> s) a t

decodeLabelled :: Array Foreign -> IOSM.InsOrdStrMap ParseExpr
decodeLabelled fs = IOSM.InsOrdStrMap $ Compose $ fs <#> unsafeCoerce >>>
  case _ of
    [s, a] -> Tuple (decodeS s) (decodeFAST (fromForeign a))
    _ -> unsafeCrashWith "Unrecognized labelled tuple"

decodeImportHashed :: FAST Foreign -> ImportHashed
decodeImportHashed (FAST r) = case r of
  { "type": "ImportHashed", "value": [a, b] } -> ImportHashed
    { importType: decodeImportType (fromForeign a)
    , hash: decodeN decodeHash b
    }
  _ -> unsafeCrashWith "Unrecognized ImportHashed"

decodeHash :: Foreign -> String
decodeHash = decodeS

decodeImportType :: FAST Foreign -> ImportType
decodeImportType (FAST r) = case r of
  { "type": "Missing" } -> Missing
  { "type": "Local", value: [t, dir, file] } ->
    let
      prefix =
        case decodeS t of
          "Absolute" -> Absolute
          "Here" -> Here
          "Home" -> Home
          _ -> unsafeCrashWith "Unrecognized FilePrefix"
    in Local prefix $ File $
    { directory: decodeDirectory dir, file: unsafeCoerce file }
  { "type": "Remote", value } -> Remote (decodeURL value)
  { "type": "Env", value: [env_var] } -> Env (decodeS env_var)
  _ -> unsafeCrashWith "Unrecognized ImportType"

decodeDirectory :: Foreign -> Directory
decodeDirectory = unsafeCoerce (Array.toUnfoldable :: Array ~> List)

decodeURL :: Array Foreign -> URL
decodeURL [scheme, authority, dir, file, query, fragment, headers ] = URL
  { scheme: case decodeS scheme of
      "http" -> HTTP
      "https" -> HTTPS
      _ -> unsafeCrashWith "Unrecognized Scheme"
  , authority: decodeS authority
  , path: File $
    { directory: decodeDirectory dir, file: unsafeCoerce file }
  , query: decodeN decodeS query
  , fragment: decodeN decodeS fragment
  , headers: decodeN (fromForeign >>> decodeImportHashed) headers
  }
decodeURL _ = unsafeCrashWith "Unrecognized URL"

disambiguate :: Array ParseExpr -> Array ParseExpr
disambiguate [] = []
disambiguate [e] = [e]
disambiguate as = as
  # Array.toUnfoldable
  # Prioritize.prioritized priorities
  # Array.fromFoldable

prioritizeVF ::
  forall s f r' r a.
    IsSymbol s =>
    Row.Cons s (FProxy f) r' r =>
  SProxy s ->
  (VariantF r a -> VariantF r a -> Maybe POrdering)
prioritizeVF s = Prioritize.fromPredicate (VariantF.on s tt ff)

pc ::
  forall s f r'.
    IsSymbol s =>
    Row.Cons s (FProxy f) r' (ExprLayerRow IOSM.InsOrdStrMap Import) =>
  SProxy s ->
  (ParseExpr -> ParseExpr -> Maybe POrdering)
pc s = prioritizeVF s `on` projectW

priorities :: ParseExpr -> ParseExpr -> Maybe POrdering
priorities = mempty
  <> pc(_s::S_ "BoolIf")
  <> Prioritize.fromRelation prioritizeEnv

prioritizeEnv :: ParseExpr -> ParseExpr -> Disj Boolean
prioritizeEnv = flip on projectW $
  \a b -> Disj $ (&&)
    do
      let isEnv (Import { importHashed: ImportHashed { importType: Env _ }}) = true
          isEnv _ = false
      a # preview AST._Embed >>> any (isEnv <<< unwrap)
    do b # preview AST._Annot >>> any
        do _.value >>> projectW >>> preview AST._Var >>> any
            do eq (AST.V "env" 0) <<< unwrap

{-
unsafePartial $ Nullable.toMaybe (Parser.parseImpl "env:Natural") <#> map Parser.decodeFAST >>> \r -> case r of [a,b] -> Parser.priorities a b
unsafePartial $ Nullable.toMaybe (Parser.parseImpl "env:Natural") <#> map Parser.decodeFAST >>> \r -> case r of [a,b] -> Parser.priorities b a

Nullable.toMaybe (Parser.parseImpl "env:Natural") <#> map Parser.decodeFAST >>> \r -> Tuple r (Parser.disambiguate r)

-}

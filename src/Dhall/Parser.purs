module Dhall.Parser where

import Prelude

import Control.Monad.Except (runExcept)
import Control.MonadZero (guard)
import Data.Array (any)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (oneOfMap)
import Data.Function (on)
import Data.Functor.Product (Product(..))
import Data.Functor.Variant (FProxy, SProxy, VariantF)
import Data.Functor.Variant as VariantF
import Data.HeytingAlgebra (ff, tt)
import Data.Identity (Identity(..))
import Data.Lens (Fold', preview)
import Data.List (List)
import Data.Maybe (Maybe(..), isJust, isNothing, maybe)
import Data.Maybe.First (First)
import Data.Monoid.Disj (Disj(..))
import Data.Newtype (unwrap)
import Data.Nullable (Nullable)
import Data.Nullable as Nullable
import Data.Symbol (class IsSymbol)
import Data.Tuple (Tuple(..))
import Dhall.Core (S_, _S)
import Dhall.Core.AST (Const(..), Expr, ExprLayerRow, TextLitF(..), Var(..), ExprLayer, projectW)
import Dhall.Core.AST as AST
import Dhall.Core.Imports.Types (Directory, File(..), FilePrefix(..), Import(..), ImportMode(..), ImportType(..), Scheme(..), URL(..))
import Dhall.Map as Dhall.Map
import Dhall.Parser.Prioritize (POrdering)
import Dhall.Parser.Prioritize as Prioritize
import Foreign (Foreign)
import Foreign as Foreign
import Partial.Unsafe (unsafeCrashWith)
import Prim.Row as Row
import Unsafe.Coerce (unsafeCoerce)

type ParseExpr = Expr Dhall.Map.InsOrdStrMap Import

parse :: String -> Maybe ParseExpr
parse s = case parseAll s <#> disambiguate of
  Just [r] -> Just r
  _ -> Nothing

parseAll :: String -> Maybe (Array ParseExpr)
parseAll s = Nullable.toMaybe (parseImpl s) <#> map decodeFAST

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
    "Sort", _ -> AST.mkConst Sort
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
    "Project", [a, b] -> AST.mkProject (decodeF a) (Left (Dhall.Map.fromFoldable (Tuple <$> decodeA decodeS b <@> unit)))
    "ProjectType", [a, b] -> AST.mkProject (decodeF a) (Right (decodeF b))
    "Merge", [a, b, c] -> AST.mkMerge (decodeF a) (decodeF b) (decodeN decodeF c)
    "ToMap", [a, b] -> AST.mkToMap (decodeF a) (decodeN decodeF b)
    "Lam", [a, b, c] -> AST.mkLam (decodeS a) (decodeF b) (decodeF c)
    "Pi", [a, b, c] -> AST.mkPi (decodeS a) (decodeF b) (decodeF c)
    "Let", [a, b, c, d] -> AST.mkLet (decodeS a) (decodeN decodeF b) (decodeF c) (decodeF d)
    "Annot", [a, b] -> AST.mkAnnot (decodeF a) (decodeF b)
    "Var", [a, b] -> AST.mkVar (V (decodeS a) (unsafeCoerce b))
    "NaturalLit", [a] -> AST.mkNaturalLit (unsafeCoerce a)
    "IntegerLit", [a] -> AST.mkIntegerLit (unsafeCoerce a)
    "DoubleLit", [a] -> AST.mkDoubleLit (unsafeCoerce a)
    "TextLit", vs -> AST.mkTextLit (decodeTextLit vs)
    "Some", [a] -> AST.mkSome (decodeF a)
    "None", _ -> AST.mkNone
    "ListLit", [a, b] -> AST.mkListLit (decodeN decodeF b) (decodeA decodeF a)
    "Record", vs -> AST.mkRecord (decodeLabelled decodeF vs)
    "RecordLit", vs -> AST.mkRecordLit (decodeLabelled decodeF vs)
    "Union", vs -> AST.mkUnion (decodeLabelled (decodeN decodeF) vs)
    "UnionLit", _
      | Just { head, tail: vs } <- Array.uncons r."value"
      , [label, value] <- decodeA identity head ->
        AST.mkUnionLit (decodeS label) (decodeF value) (decodeLabelled decodeF vs)
    "Assert", [a] -> AST.mkAssert (decodeF a)
    "Equivalent", [a, b] -> AST.mkEquivalent (decodeF a) (decodeF b)
    "Hashed", [a, b] -> AST.mkHashed (decodeF a) (decodeHash b)
    "Import", [a, b] -> case decodeImportType (fromForeign a) of
      Tuple mb importType ->
        (maybe identity (flip AST.mkUsingHeaders <<< decodeFAST) mb) $
          pure $ Import
            { importType
            , importMode: case runExcept $ Foreign.readString b of
                Right "Text" -> RawText
                Right "Location" -> Location
                _ -> Code
            }
    _, _ -> unsafeCrashWith $ "Unrecognized Expr: " <> r."type" <> " " <> unsafeCoerce r

decodeTextLit :: Array Foreign -> TextLitF ParseExpr
decodeTextLit = Array.foldr f (TextLit "") where
  f next result = case runExcept (Foreign.readString next) of
    Left _ -> TextInterp "" (decodeFAST (fromForeign next)) result
    Right s' ->
      case result of
        TextLit s -> TextLit (s' <> s)
        TextInterp s a t -> TextInterp (s' <> s) a t

decodeLabelled :: forall a. (Foreign -> a) -> Array Foreign -> Dhall.Map.InsOrdStrMap a
decodeLabelled dec fs = Dhall.Map.mkIOSM $ fs <#> unsafeCoerce >>>
  case _ of
    [s, a] -> Tuple (decodeS s) (dec a)
    _ -> unsafeCrashWith "Unrecognized labelled tuple"

decodeHash :: Foreign -> String
decodeHash = decodeS

decodeImportType :: FAST Foreign -> Tuple (Maybe (FAST Foreign)) ImportType
decodeImportType (FAST r) = case r of
  { "type": "Missing" } -> Tuple Nothing Missing
  { "type": "Local", value: [t, dir, file] } ->
    let
      prefix =
        case decodeS t of
          "Absolute" -> Absolute
          "Here" -> Here
          "Parent" -> Parent
          "Home" -> Home
          _ -> unsafeCrashWith "Unrecognized FilePrefix"
    in Tuple Nothing $ Local prefix $ File $
    { directory: decodeDirectory dir, file: unsafeCoerce file }
  { "type": "Remote", value } -> Remote <$> decodeURL value
  { "type": "Env", value: [env_var] } -> Tuple Nothing $ Env (decodeS env_var)
  _ -> unsafeCrashWith "Unrecognized ImportType"

decodeDirectory :: Foreign -> Directory
decodeDirectory = unsafeCoerce ((Array.reverse >>> Array.toUnfoldable) :: Array ~> List)

decodeURL :: Array Foreign -> Tuple (Maybe (FAST Foreign)) URL
decodeURL [ scheme, authority, dir, file, query, headers ] =
  Tuple (decodeN fromForeign headers) $
  URL
  { scheme: case decodeS scheme of
      "http" -> HTTP
      "https" -> HTTPS
      _ -> unsafeCrashWith "Unrecognized Scheme"
  , authority: decodeS authority
  , path: File $
    { directory: decodeDirectory dir, file: unsafeCoerce file }
  , query: decodeN decodeS query
  , headers: Nothing
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

firstVar :: ParseExpr -> Maybe AST.Var
firstVar e = e # projectW #
  VariantF.on (_S::S_ "Var") (pure <<< unwrap) (oneOfMap firstVar)

pc ::
  forall s f r'.
    IsSymbol s =>
    Row.Cons s (FProxy f) r' (ExprLayerRow Dhall.Map.InsOrdStrMap Import) =>
  SProxy s ->
  (ParseExpr -> ParseExpr -> Maybe POrdering)
pc s = prioritizeVF s `on` projectW

keyword ::
  forall s f r'.
    IsSymbol s =>
    Row.Cons s (FProxy f) r' (ExprLayerRow Dhall.Map.InsOrdStrMap Import) =>
  SProxy s ->
  String ->
  (ParseExpr -> ParseExpr -> Maybe POrdering)
keyword s var = Prioritize.fromLRPredicates
  do projectW >>> VariantF.on s tt ff
  do \b -> firstVar b == Just (AST.V var 0)

-- This will compare two notes to determine their priorities.
-- Must be applied recursively through Prioritize.prioritize and helpers
priorities :: ParseExpr -> ParseExpr -> Maybe POrdering
priorities e1 e2 = (\f -> f e1 e2)
  do mempty
      <> keyword (_S::S_ "BoolIf") "if"
      <> prioritize_forall
      <> prioritize_env
      <> prioritize_annot

-- True if the left expression is more or equally prioritized than the right.
isPrioritized :: ParseExpr -> ParseExpr -> Boolean
isPrioritized e1 e2 = Prioritize.isPrioritized priorities e1 e2
-- it's an arrow that points to the prioritized element <
-- which is on the + side
-- (as opposed to the worse one on the - side)
-- but it also returns true for equality, so there's =
infix 9 isPrioritized as <+-=

-- Reveal the shape of a node if it matches the right constructor
reveal :: forall a.
  (Fold' (First a) (ExprLayer Dhall.Map.InsOrdStrMap Import) a) ->
  Expr Dhall.Map.InsOrdStrMap Import ->
  Maybe a
reveal cons = projectW >>> preview cons

-- Check if it fits the pattern, based on the constructor and the condition
-- of the constructor data
fits :: forall a.
  (Fold' (First a) (ExprLayer Dhall.Map.InsOrdStrMap Import) a) ->
  (a -> Boolean) ->
  Expr Dhall.Map.InsOrdStrMap Import ->
  Boolean
fits cons pred = reveal cons >>> any pred

-- Disambiguate `forall (v : ?t) -> ?b` from `(forall@0 (v@0 : ?t)) -> ?b`
prioritize_forall :: ParseExpr -> ParseExpr -> Maybe POrdering
prioritize_forall = Prioritize.fromRelation \better worse -> Disj $ isJust do
  { var, ty, body } <- reveal AST._Pi better
  { var: var', ty: _forall_app, body: body'} <- reveal AST._Pi worse
  guard $ var' == "_"
  guard $ body <+-= body'
  { fn: _forall, arg: var_annot } <- reveal AST._App _forall_app
  guard $ _forall == AST.mkVar (AST.V "forall" 0)
  { value: _var, ty: ty' } <- reveal AST._Annot var_annot
  guard $ _var == AST.mkVar (AST.V var 0)
  guard $ ty <+-= ty'

prioritize_env :: ParseExpr -> ParseExpr -> Maybe POrdering
prioritize_env = Prioritize.fromLRPredicates
  do
    let isEnv (Import { importType: Env _ }) = true
        isEnv _ = false
    fits AST._Embed $ unwrap >>> isEnv
  do
    fits AST._Annot $ flip compose _.value $
      fits AST._Var $ unwrap >>> eq (AST.V "env" 0)

prioritize_annot :: ParseExpr -> ParseExpr -> Maybe POrdering
prioritize_annot = Prioritize.fromRelation \better worse -> Array.foldMap (Disj <<< isJust)
  [ do
      AST.MergeF x y ma <- reveal AST._Merge better
      a <- ma
      { value: xy', ty: a' } <- reveal AST._Annot worse
      AST.MergeF x' y' mb <- reveal AST._Merge xy'
      guard $ isNothing mb
      guard $ x <+-= x'
      guard $ y <+-= y'
  , do
      Product (Tuple (Identity x) ma) <- reveal AST._ToMap better
      a <- ma
      { value: xy', ty: a' } <- reveal AST._Annot worse
      Product (Tuple (Identity x') mb) <- reveal AST._ToMap xy'
      guard $ isNothing mb
      guard $ x <+-= x'
  ]

{-
unsafePartial $ Nullable.toMaybe (Parser.parseImpl "env:Natural") <#> map Parser.decodeFAST >>> \r -> case r of [a,b] -> Parser.priorities a b
unsafePartial $ Nullable.toMaybe (Parser.parseImpl "env:Natural") <#> map Parser.decodeFAST >>> \r -> case r of [a,b] -> Parser.priorities b a

Nullable.toMaybe (Parser.parseImpl "env:Natural") <#> map Parser.decodeFAST >>> \r -> Tuple r (Parser.disambiguate r)

-}

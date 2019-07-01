module Dhall.Core.CBOR where

import Prelude

import Control.MonadZero (guard)
import Control.Plus (empty)
import Data.Argonaut.Core (Json)
import Data.Argonaut.Core as J
import Data.Array (any, fold)
import Data.Array as Array
import Data.Const (Const(..))
import Data.Functor.App (App(..))
import Data.Functor.Product (Product(..))
import Data.Functor.Variant as VariantF
import Data.HeytingAlgebra (tt)
import Data.Identity (Identity(..))
import Data.Int as Int
import Data.List (List)
import Data.Maybe (Maybe(..), maybe)
import Data.Natural (intToNat, natToInt)
import Data.Newtype (un)
import Data.Traversable (traverse)
import Data.TraversableWithIndex (traverseWithIndex)
import Data.Tuple (Tuple(..), fst)
import Dhall.Core (Const(..), Expr, Import(..), ImportType(..), LetF(..), MergeF(..), Pair(..), S_, TextLitF(..), Triplet(..), Var(..), _S)
import Dhall.Core.AST (BindingBody(..), projectW)
import Dhall.Core.AST as AST
import Dhall.Core.AST.Types.Basics (pureTextLitF)
import Dhall.Core.Imports.Types (Directory(..), File(..), FilePrefix(..), ImportHashed(..), ImportMode(..), Scheme(..), URL(..))
import Dhall.Core.StrMapIsh (class StrMapIsh)
import Dhall.Core.StrMapIsh as StrMapIsh
import Foreign.Object as Foreign.Object

encode :: forall m. StrMapIsh m => Expr m Import -> Json
encode = projectW >>> VariantF.match
  { "Var": un Const >>> case _ of
      V "_" n -> int n
      V x n -> J.fromArray [ J.fromString x, int n ]
  , "NaturalBuild": pure $ J.fromString "Natural/build"
  , "NaturalFold": pure $ J.fromString "Natural/fold"
  , "NaturalIsZero": pure $ J.fromString "Natural/isZero"
  , "NaturalEven": pure $ J.fromString "Natural/even"
  , "NaturalOdd": pure $ J.fromString "Natural/odd"
  , "NaturalToInteger": pure $ J.fromString "Natural/toInteger"
  , "NaturalShow": pure $ J.fromString "Natural/show"
  , "IntegerToDouble": pure $ J.fromString "Integer/toDouble"
  , "IntegerShow": pure $ J.fromString "Integer/show"
  , "DoubleShow": pure $ J.fromString "Double/show"
  , "ListBuild": pure $ J.fromString "List/build"
  , "ListFold": pure $ J.fromString "List/fold"
  , "ListLength": pure $ J.fromString "List/length"
  , "ListHead": pure $ J.fromString "List/head"
  , "ListLast": pure $ J.fromString "List/last"
  , "ListIndexed": pure $ J.fromString "List/indexed"
  , "ListReverse": pure $ J.fromString "List/reverse"
  , "OptionalFold": pure $ J.fromString "Optional/fold"
  , "OptionalBuild": pure $ J.fromString "Optional/build"
  -- , "TextShow": pure $ J.fromString "Text/show"
  , "Bool": pure $ J.fromString "Bool"
  , "Optional": pure $ J.fromString "Optional"
  , "None": pure $ J.fromString "None"
  , "Natural": pure $ J.fromString "Natural"
  , "Integer": pure $ J.fromString "Integer"
  , "Double": pure $ J.fromString "Double"
  , "Text": pure $ J.fromString "Text"
  , "List": pure $ J.fromString "List"
  , "Const": un Const >>> case _ of
      Type -> J.fromString "Type"
      Kind -> J.fromString "Kind"
  , "App": \(Pair f z) -> tagged 0 $
      let
        rec a = a # projectW # VariantF.on (_S::S_ "App")
          (\(Pair f' y) -> rec f' <> [encode y])
          (\_ -> [encode a])
      in rec f <> [encode z]
  , "Lam": \(BindingBody name ty body) -> tagged 1 $
      (if name == "_" then [] else [ J.fromString name ]) <>
      [ encode ty, encode body ]
  , "Pi": \(BindingBody name ty body) -> tagged 2 $
      (if name == "_" then [] else [ J.fromString name ]) <>
      [ encode ty, encode body ]
  , "BoolOr": operator 0
  , "BoolAnd": operator 1
  , "BoolEQ": operator 2
  , "BoolNE": operator 3
  , "NaturalPlus": operator 4
  , "NaturalTimes": operator 5
  , "TextAppend": operator 6
  , "ListAppend": operator 7
  , "Combine": operator 8
  , "Prefer": operator 9
  , "CombineTypes": operator 10
  , "ImportAlt": operator 11
  , "ListLit": \(Product (Tuple ty vals)) -> tagged 4
      case vals of
        [] -> [ maybe null encode ty ]
        _ -> [ null ] <> map encode vals
  , "Some": \(Identity val) -> tagged 5 [ null, encode val ]
  , "Merge": \(MergeF rec val mty) -> tagged 6
      case mty of
        Nothing -> [ encode rec, encode val ]
        Just ty -> [ encode rec, encode val, encode ty ]
  , "Record": \m -> tagged 7 [ toObject $ encode <$> m ]
  , "RecordLit": \m -> tagged 8 [ toObject $ encode <$> m ]
  , "Field": \(Tuple name expr) -> tagged 9 [ encode expr, J.fromString name ]
  -- TODO: project by type
  , "Project": \(Tuple (App names) expr) -> tagged 10 $ [ encode expr ] <>
      (J.fromString <<< fst <$> StrMapIsh.toUnfoldable names)
  , "Union": \m -> tagged 11 [ toObject $ encode <$> m ]
  , "UnionLit": \(Product (Tuple (Tuple name val) m)) -> tagged 12
      [ J.fromString name, encode val, toObject $ encode <$> m ]
  , "BoolLit": un Const >>> J.fromBoolean
  , "BoolIf": \(Triplet t l r) -> tagged 14 $ encode <$> [ t, l, r ]
  , "NaturalLit": tagged 15 <<< pure <<< un Const >>> natToInt >>> Int.toNumber >>> J.fromNumber
  , "IntegerLit": tagged 16 <<< pure <<< un Const >>> Int.toNumber >>> J.fromNumber
  -- TODO
  , "DoubleLit": un Const >>> J.fromNumber
  , "Embed": un Const >>> encodeImport
  , "TextLit": \m ->
      let
        rec (TextLit s) = [ J.fromString s ]
        rec (TextInterp s a m') = [ J.fromString s, encode a ] <> rec m'
      in tagged 18 (rec m)
  -- TODO
  , "Let": \(LetF name mty val expr) -> tagged 25 $
      [ J.fromString name, maybe null encode mty, encode val ] <> [ encode expr ]
  , "Annot": \(Pair val ty) -> tagged 26 [ encode val, encode ty ]
  , "Constructors": \(Identity v) -> tagged 13 [ encode v ]
  , "OptionalLit": \(Product (Tuple (Identity ty) mval)) ->
      case mval of
        Nothing -> tagged 0 [ J.fromString "None", encode ty ]
        Just val -> tagged 5 [ null, encode val ]
  }

null :: Json
null = J.jsonNull
int :: Int -> Json
int = J.fromNumber <<< Int.toNumber
tagged :: Int -> Array Json -> Json
tagged t a = J.fromArray $ [ int t ] <> a
operator :: forall m. StrMapIsh m => Int -> Pair (Expr m Import) -> Json
operator t (Pair l r) = J.fromArray $ [ int 3, int t, encode l, encode r ]
toObject :: forall m. StrMapIsh m => m Json -> Json
toObject = StrMapIsh.toUnfoldable
  >>> (identity :: List ~> List)
  >>> Foreign.Object.fromFoldable
    >>> J.fromObject
fromObject :: forall m. StrMapIsh m => Json -> Maybe (m Json)
fromObject = pure
  <<< StrMapIsh.fromFoldable
  <<< (identity :: List ~> List)
  <<< Foreign.Object.toUnfoldable
    <=< J.toObject

decodeTag :: Json -> Maybe Int
decodeTag head = do
  tagN <- J.toNumber head
  let tagI = Int.floor tagN
  guard $ tagI >= 0
  guard $ tagN == Int.toNumber tagI
  pure tagI

encodeImport :: Import -> Json
encodeImport = case _ of
  Import
    { importHashed: ImportHashed
      { hash, importType }
    , importMode
    } -> tagged 24 $
      -- TODO: bytestring
      [ maybe null (("\x12\x20" <> _) >>> J.fromString) hash ] <>
      [ int case importMode of
          Code -> 0
          RawText -> 1
      ] <> case importType of
        Remote (URL url@{ path: File { directory: Directory dirs, file } }) ->
          [ int case url.scheme of
              HTTP -> 0
              HTTPS -> 1
          ] <> [ maybe null (encodeImport <<< \i -> Import { importHashed: i, importMode: Code }) url.headers ] <>
          [ J.fromString url.authority ] <> Array.reverse (Array.fromFoldable $ J.fromString <$> dirs) <>
          [ J.fromString file ] <>
          [maybe null J.fromString url.query ]
        Local pre (File { directory: Directory dirs, file }) ->
          [ int case pre of
              Absolute -> 2
              Here -> 3
              Parent -> 4
              Home -> 5
          ] <> Array.reverse (Array.fromFoldable $ J.fromString <$> dirs) <>
          [ J.fromString file ]
        Env var -> [ int 6, J.fromString var ]
        Missing -> [ int 7 ]

decodeImport :: Array Json -> Maybe Import
decodeImport q = do
  { head: tag, tail: q0 } <- Array.uncons q
  guard $ decodeTag tag == Just 24
  { head: hash', tail: q1 } <- Array.uncons q0
  hash <- case J.toNull hash' of
    Just _ -> pure Nothing
    -- TODO: hash
    Nothing -> Just <$> J.toString hash'
  -- TODO: Location
  { head: importMode', tail: q2 } <- Array.uncons q1
  importMode <- decodeTag importMode' >>= case _ of
    0 -> Just Code
    1 -> Just RawText
    _ -> Nothing
  { head: importType', tail: q3 } <- Array.uncons q2
  let
    remote scheme = (Remote <<< URL) <$> do
      { head: headers', tail: q4 } <- Array.uncons q3
      { head: authority', tail: q5 } <- Array.uncons q4
      { init: path', last: query' } <- Array.unsnoc q5
      { init, last } <- Array.unsnoc path'
      headers <- case J.toNull headers' of
        Just _ -> Nothing
        Nothing -> case J.toArray headers' >>= decodeImport of
          Just (Import { importHashed: i, importMode: Code }) ->
            pure (Just i)
          _ -> empty
      authority <- J.toString authority'
      file <- J.toString last
      dirs <- (Array.toUnfoldable <<< Array.reverse) <$> traverse J.toString init
      let path = File { directory: Directory dirs, file }
      query <- case J.toNull query' of
        Just _ -> Nothing
        Nothing -> Just <$> J.toString query'
      pure { scheme, headers, authority, path, query }

    local pre = Local pre <$> do
      { init, last } <- Array.unsnoc q3
      file <- J.toString last
      dirs <- (Array.toUnfoldable <<< Array.reverse) <$> traverse J.toString init
      pure (File { directory: Directory dirs, file })

    env = case q3 of
      [ var ] -> Env <$> J.toString var
      _ -> empty

    missing = pure Missing
  importType <- decodeTag importType' >>= case _ of
    0 -> remote HTTP
    1 -> remote HTTPS
    2 -> local Absolute
    3 -> local Here
    4 -> local Parent
    5 -> local Home
    6 -> env
    7 -> missing
    _ -> empty

  pure $
    Import
      { importHashed: ImportHashed
        { hash, importType }
      , importMode
      }

decode :: forall m. StrMapIsh m => Json -> Maybe (Expr m Import)
decode = J.caseJson
  (pure empty)
  (pure <<< AST.mkBoolLit)
  -- TODO: distinguish number types???
  (pure <<< AST.mkDoubleLit)
  builtin
  (\a -> do
    { head, tail } <- Array.uncons a
    tag <- decodeTag head
    decodeTagged tag tail
  )
  (pure empty)
  where
    builtin = case _ of
      "Natural/build" -> pure AST.mkNaturalBuild
      "Natural/fold" -> pure AST.mkNaturalFold
      "Natural/isZero" -> pure AST.mkNaturalIsZero
      "Natural/even" -> pure AST.mkNaturalEven
      "Natural/odd" -> pure AST.mkNaturalOdd
      "Natural/toInteger" -> pure AST.mkNaturalToInteger
      "Natural/show" -> pure AST.mkNaturalShow
      "Integer/toDouble" -> pure AST.mkIntegerToDouble
      "Integer/show" -> pure AST.mkIntegerShow
      "Double/show" -> pure AST.mkDoubleShow
      "List/build" -> pure AST.mkListBuild
      "List/fold" -> pure AST.mkListFold
      "List/length" -> pure AST.mkListLength
      "List/head" -> pure AST.mkListHead
      "List/last" -> pure AST.mkListLast
      "List/indexed" -> pure AST.mkListIndexed
      "List/reverse" -> pure AST.mkListReverse
      "Optional/fold" -> pure AST.mkOptionalFold
      "Optional/build" -> pure AST.mkOptionalBuild
      -- "Text/show" -> pure AST.mkTextShow
      "Bool" -> pure AST.mkBool
      "Optional" -> pure AST.mkOptional
      "None" -> pure AST.mkNone
      "Natural" -> pure AST.mkNatural
      "Integer" -> pure AST.mkInteger
      "Double" -> pure AST.mkDouble
      "Text" -> pure AST.mkText
      "List" -> pure AST.mkList
      "Type" -> pure AST.mkType
      "Kind" -> pure AST.mkKind
      _ -> empty
    decodeMaybe j = case J.toNull j of
      Just _ -> pure Nothing
      Nothing -> Just <$> decode j
    decodeTagged :: Int -> Array Json -> Maybe (Expr m Import)
    decodeTagged = case _ of
      0 -> case _ of
        [] -> empty
        [ _ ] -> empty
        [ f, a ] -> AST.mkApp <$> decode f <*> decode a
        q -> do
          { head, tail } <- Array.uncons q
          f0 <- decode head
          as <- traverse decode tail
          pure $ Array.foldl AST.mkApp f0 as
      1 -> case _ of
        [ ty, body ] -> AST.mkLam "_" <$> decode ty <*> decode body
        [ name, ty, body ] -> do
          name' <- J.toString name
          guard $ name' /= "_"
          AST.mkLam name' <$> decode ty <*> decode body
        _ -> empty
      2 -> case _ of
        [ ty, body ] -> AST.mkPi "_" <$> decode ty <*> decode body
        [ name, ty, body ] -> do
          name' <- J.toString name
          guard $ name' /= "_"
          AST.mkPi name' <$> decode ty <*> decode body
        _ -> empty
      3 -> case _ of
        [ op, l, r ] -> do
          op' <- decodeTag op
          l' <- decode l
          r' <- decode r
          c <- case op' of
            0 -> pure AST.mkBoolOr
            1 -> pure AST.mkBoolAnd
            2 -> pure AST.mkBoolEQ
            3 -> pure AST.mkBoolNE
            4 -> pure AST.mkNaturalPlus
            5 -> pure AST.mkNaturalTimes
            6 -> pure AST.mkTextAppend
            7 -> pure AST.mkListAppend
            8 -> pure AST.mkCombine
            9 -> pure AST.mkPrefer
            10 -> pure AST.mkCombineTypes
            11 -> pure AST.mkImportAlt
            _ -> empty
          pure $ c l' r'
        _ -> empty
      4 -> \q -> do
        { head, tail } <- Array.uncons q
        head' <- decodeMaybe head
        tail' <- traverse decode tail
        guard $ any tt head' || any tt tail'
        pure $ AST.mkListLit head' tail'
      5 -> case _ of
        [ nll, t ] -> do
          J.toNull nll
          AST.mkSome <$> decode t
        _ -> empty
      6 -> case _ of
        [ rec, val ] -> AST.mkMerge <$> decode rec <*> decode val <@> Nothing
        [ rec, val, ty ] ->
          AST.mkMerge <$> decode rec <*> decode val <*> (Just <$> decode ty)
        _ -> empty
      7 -> case _ of
        [ m ] -> do
          m' <- fromObject m
          AST.mkRecord <$> traverse decode m'
        _ -> empty
      8 -> case _ of
        [ m ] -> do
          m' <- fromObject m
          AST.mkRecordLit <$> traverse decode m'
        _ -> empty
      9 -> case _ of
        [ expr, name ] -> do
          expr' <- decode expr
          name' <- J.toString name
          pure $ AST.mkField expr' name'
        _ -> empty
      -- TODO: project by type
      10 -> \q -> do
        { head, tail } <- Array.uncons q
        expr' <- decode head
        tail' <- traverse J.toString tail
        let names' = StrMapIsh.fromFoldable $ Tuple <$> tail' <@> unit
        pure $ AST.mkProject expr' names'
      11 -> case _ of
        [ m ] -> do
          m' <- fromObject m
          AST.mkUnion <$> traverse decode m'
        _ -> empty
      12 -> case _ of
        [ name, val, m ] -> do
          name' <- J.toString name
          val' <- decode val
          m' <- fromObject m
          AST.mkUnionLit name' val' <$> traverse decode m'
        _ -> empty
      14 -> case _ of
        [ t, l, r ] -> AST.mkBoolIf <$> decode t <*> decode l <*> decode r
        _ -> empty
      15 -> case _ of
        [ n ] -> do
          n' <- J.toNumber n >>= Int.fromNumber >>> map intToNat
          pure $ AST.mkNaturalLit n'
        _ -> empty
      16 -> case _ of
        [ n ] -> do
          n' <- J.toNumber n >>= Int.fromNumber
          pure $ AST.mkIntegerLit n'
        _ -> empty
      18 ->
        map (AST.mkTextLit <<< fold) <<< traverseWithIndex \i ->
          if Int.even i
            then J.toString >=> TextLit >>> pure
            else decode >=> pureTextLitF >>> pure
      24 -> ([ J.fromNumber 24.0 ] <> _) >>> decodeImport >>> map pure
      -- TODO
      25 -> case _ of
        [ name, mty, val, expr ] -> do
          AST.mkLet <$> J.toString name <*> decodeMaybe mty <*> decode val <*> decode expr
        _ -> empty
      26 -> case _ of
        [ val, ty ] -> AST.mkAnnot <$> decode val <*> decode ty
        _ -> empty
      13 -> case _ of
        [ v ] -> AST.mkConstructors <$> decode v
        _ -> empty
      _ -> pure empty

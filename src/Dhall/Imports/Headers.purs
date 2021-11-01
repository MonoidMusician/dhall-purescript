module Dhall.Imports.Headers where

import Prelude

import Control.Alt (class Alt, (<|>))
import Control.Alternative (guard)
import Control.Plus (empty)
import Data.Const (Const(..))
import Data.Foldable (oneOfMap)
import Data.Functor.Variant as VariantF
import Data.Lens as Lens
import Data.List (List(..), foldr, (:))
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Dhall.Core.AST (S_, _S, Expr)
import Dhall.Core.AST as AST
import Dhall.Core.Imports (Header, Headers, Import(..), ImportMode(..), ImportType(..), parseLocal, prettyFile, prettyFilePrefix, prettyURL)
import Dhall.Map (class MapLike)
import Dhall.Map as Dhall.Map


locationType :: forall m a. MapLike String m => AST.Expr m a
locationType = AST.mkUnion $ Dhall.Map.fromFoldable $
  [ Tuple "Environment" $ Just AST.mkText
  , Tuple "Local" $ Just AST.mkText
  , Tuple "Missing" $ Nothing
  , Tuple "Remote" $ Just AST.mkText
  ]

fromLocation :: forall m a. MapLike String m => ImportType -> AST.Expr m a
fromLocation = case _ of
  Missing -> AST.mkField locationType "Missing"
  Env e -> AST.mkApp (AST.mkField locationType "Environment") $ AST.mkTextLit' e
  Local pre l -> AST.mkApp (AST.mkField locationType "Local") $ AST.mkTextLit' $
    prettyFilePrefix pre <> prettyFile l
  Remote url ->
    AST.mkApp (AST.mkField locationType "Remote") $ AST.mkTextLit' $
      prettyURL url


headerType :: forall m a. MapLike String m => Expr m a
headerType = AST.mkRecord $ Dhall.Map.fromFoldable $
  [ Tuple "mapKey" AST.mkText
  , Tuple "mapValue" AST.mkText
  ]

toHeaders :: forall m a. MapLike String m => Expr m a -> Maybe Headers
toHeaders = AST.projectW >>> Lens.preview AST._ListLit
  >=> _.values >>> traverse toHeader

toHeader :: forall m a. MapLike String m => Expr m a -> Maybe Header
toHeader = AST.projectW >>> Lens.preview AST._RecordLit >=>
  \m ->
    let
      getLit = AST.projectW >>> Lens.preview AST._TextLit_single
    in { header: _, value: _ }
      <$> (getLit =<< Dhall.Map.get "mapKey" m)
      <*> (getLit =<< Dhall.Map.get "mapValue" m)

fromHeaders :: forall m a. MapLike String m => Headers -> Expr m a
fromHeaders [] = AST.mkListLit (Just headerType) []
fromHeaders headers = AST.mkListLit Nothing $ fromHeader <$> headers

fromHeader :: forall m a. MapLike String m => Header -> Expr m a
fromHeader { header, value } = AST.mkRecordLit $ Dhall.Map.fromFoldable
  [ Tuple "mapKey" $ AST.mkTextLit' header
  , Tuple "mapValue" $ AST.mkTextLit' value
  ]

appendHeader :: forall m a. MapLike String m => Expr m a -> Expr m a -> Expr m a
appendHeader a b
  | Just { values: x } <- Lens.preview AST._ListLit (AST.projectW a)
  , Just { values: y } <- Lens.preview AST._ListLit (AST.projectW b) =
    let xy = x <> y in
    case xy of
      [] -> AST.mkListLit (Just headerType) []
      _ -> AST.mkListLit Nothing xy
appendHeader a b = AST.mkListAppend a b

getFromOriginHeaders :: forall m i. MapLike String m => String -> Expr m i -> Headers
getFromOriginHeaders origin originHeaders = fromMaybe empty do
  items <- Lens.preview AST._ListLit (AST.projectW originHeaders) <#> _.values
  items # oneOfMap \item -> do
    entry <- Lens.preview AST._RecordLit (AST.projectW item)
    entryOrigin <- Lens.preview AST._TextLit_single <<< AST.projectW =<< Dhall.Map.get "mapKey" entry
    guard $ entryOrigin == origin
    Dhall.Map.get "mapValue" entry >>= toHeaders

desugarHeaders :: forall m. MapLike String m => Expr m Import -> Expr m Import
desugarHeaders = go Nil where
  go headers expr = AST.embedW $ let exprF = AST.projectW expr in
    VariantF.onMatch
      { "Embed": \(Const (Import i)) ->
          let
            new = VariantF.inj (_S::S_ "Embed") $ Const $ Import i
            headers0 = AST.mkListLit (Just headerType) []
          in case i.importType of
            Remote _
              | head <- foldr appendHeader headers0 headers
              , head /= headers0
                -> VariantF.inj (_S::S_ "UsingHeaders") $
                    AST.Pair (AST.embedW new) head
            _ -> new
      , "UsingHeaders": \(AST.Pair e headers') ->
          AST.projectW $ go (go Nil headers' : headers) e
      } (\_ -> go headers <$> exprF) exprF



originHeadersType :: forall m i. MapLike String m => Expr m i
originHeadersType = AST.mkApp AST.mkList $ AST.mkRecord $ Dhall.Map.fromFoldable $
  [ Tuple "mapKey" AST.mkText
  , Tuple "mapValue" $ AST.mkApp AST.mkList headerType
  ]

emptyOriginHeaders :: forall m i. MapLike String m => Expr m i
emptyOriginHeaders = AST.mkListLit (Just originHeadersType) []

envOriginHeaders :: Import
envOriginHeaders = Import
  { importMode: Code
  , importType: Env "DHALL_HEADERS"
  }

originHeadersFromLocation :: forall m. MapLike String m => String -> Expr m Import
originHeadersFromLocation file =
  AST.mkImportAlt (pure envOriginHeaders)
    (pure (Import { importMode: Code, importType: parseLocal file }))

originHeadersFromLocationAff :: forall f m.
  Functor f => Alt f => Applicative f =>
  MapLike String m => f String -> f (Expr m Import)
originHeadersFromLocationAff fileAff =
  map originHeadersFromLocation fileAff <|> pure (pure envOriginHeaders)

allOriginHeaders :: forall m. MapLike String m => Expr m Import -> Expr m Import
allOriginHeaders e =
  AST.mkAnnot (AST.mkImportAlt e emptyOriginHeaders) originHeadersType

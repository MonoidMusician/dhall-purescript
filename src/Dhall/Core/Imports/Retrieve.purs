module Dhall.Core.Imports.Retrieve where

import Prelude

import Control.Plus (empty)
import Data.Functor.Product (Product(..))
import Data.Functor.Variant as VariantF
import Data.Maybe (Maybe)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Dhall.Core (Expr, S_, TextLitF(..), _S)
import Dhall.Core.AST (mkRecord, mkText, projectW)
import Dhall.Core.Imports.Types (Headers, Header)
import Dhall.Core.StrMapIsh (class StrMapIsh)
import Dhall.Core.StrMapIsh as StrMapIsh
import Effect.Aff (Aff)
import Foreign.Object as Foreign.Object
import Milkis as M
import Milkis.Impl (FetchImpl)
import Milkis.Impl.Node (nodeFetch)
import Milkis.Impl.Window (windowFetch)
import Node.Encoding (Encoding(UTF8))
import Node.FS.Aff as Node.FS.Aff

nodeRetrieveFile :: String -> Aff String
nodeRetrieveFile = Node.FS.Aff.readTextFile UTF8

milkisRetrieveURL :: FetchImpl -> Headers -> String -> Aff String
milkisRetrieveURL impl headers = M.URL >>> (=<<) M.text <<< flip (M.fetch impl)
  { method: M.getMethod
  , headers: Foreign.Object.fromFoldable
      (headers <#> \{ header, value } -> Tuple header value)
  }

nodeRetrieveURL :: Headers -> String -> Aff String
nodeRetrieveURL = milkisRetrieveURL nodeFetch

windowRetrieveURL :: Headers -> String -> Aff String
windowRetrieveURL = milkisRetrieveURL windowFetch

headerType :: forall m a. StrMapIsh m => Expr m a
headerType = mkRecord $ StrMapIsh.fromFoldable $
  [ Tuple "header" mkText
  , Tuple "value"  mkText
  ]

toHeaders :: forall m a. StrMapIsh m => Expr m a -> Maybe Headers
toHeaders = projectW >>> flip (VariantF.on (_S::S_ "ListLit")) (pure empty)
  \(Product (Tuple _ items)) -> traverse toHeader items

toHeader :: forall m a. StrMapIsh m => Expr m a -> Maybe Header
toHeader = projectW >>> flip (VariantF.on (_S::S_ "RecordLit")) (pure empty)
  \m ->
    let
      getLit = projectW >>> flip (VariantF.on (_S::S_ "TextLit")) (pure empty)
        case _ of
          TextLit s -> pure s
          _ -> empty
    in { header: _, value: _ }
      <$> (getLit =<< StrMapIsh.get "header" m)
      <*> (getLit =<< StrMapIsh.get "value" m)

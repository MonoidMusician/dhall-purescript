module Dhall.Imports.Retrieve where

import Prelude

import Control.Plus (empty)
import Data.Array as Array
import Data.ArrayBuffer.Types (ArrayBuffer)
import Data.Const (Const(..))
import Data.Foldable (oneOfMap)
import Data.Functor.Product (Product(..))
import Data.Functor.Variant as VariantF
import Data.Lens as Lens
import Data.List (List(..), foldr, (:))
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Dhall.Core.AST (S_, _S)
import Dhall.Core.AST as AST
import Dhall.Core.Imports (Directory(..), File(..), FilePrefix(..), Header, Headers, Import(..), ImportType(..), getHeaders, prettyFile, prettyFilePrefix, prettyURL)
import Dhall.Map (class MapLike)
import Dhall.Map as Dhall.Map
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Foreign.Object as Foreign.Object
import Milkis as M
import Milkis.Impl (FetchImpl)
import Node.Buffer as Node.Buffer
import Node.Encoding (Encoding(UTF8))
import Node.FS.Aff as Node.FS.Aff

foreign import getEnv :: Effect (Foreign.Object.Object String)

lookupEnv :: String -> Effect (Maybe String)
lookupEnv k = Foreign.Object.lookup k <$> getEnv

nodeRetrieveEnv :: String -> Aff String
nodeRetrieveEnv name = liftEffect $ lookupEnv name >>= case _ of
  Nothing -> throw $ "Unknown envionment variable: " <> name
  Just v -> pure v

nodeRetrieveFile :: String -> Aff String
nodeRetrieveFile path = Node.FS.Aff.readTextFile UTF8 path

foreign import responseHeaders :: M.Response -> M.Headers
foreign import nodeFetch :: Unit -> FetchImpl
foreign import windowFetch :: Unit -> FetchImpl

milkisRetrieveURL :: FetchImpl -> Headers -> String -> Aff { result :: String, headers :: Headers }
milkisRetrieveURL impl headers = M.URL >>> (=<<) infos <<< flip (M.fetch impl)
  { method: M.getMethod
  -- FIXME: duplicate headers
  , headers: Foreign.Object.fromFoldable
      (headers <#> \{ header, value } -> Tuple header value)
  } where
    infos resp = do
      result <- M.text resp
      let resHeaders = Foreign.Object.toUnfoldable (responseHeaders resp) <#>
            \(Tuple header value) -> { header, value }
      pure { result, headers: resHeaders }

nodeRetrieveURL :: Headers -> String -> Aff { result :: String, headers :: Headers }
nodeRetrieveURL headers url = milkisRetrieveURL (nodeFetch unit) headers url

windowRetrieveURL :: Headers -> String -> Aff { result :: String, headers :: Headers }
windowRetrieveURL headers url = milkisRetrieveURL (windowFetch unit) headers url

moveHere :: String -> ImportType -> ImportType
moveHere _ i@(Local Absolute _) = i
moveHere _ i@(Local Home _) = i
moveHere here (Local Parent (File { directory, file })) =
  let adddir = Directory $ (Array.toUnfoldable <<< Array.reverse) $ String.split (String.Pattern "/") (here <> "/..")
  in Local Here (File { directory: adddir <> directory, file })
moveHere here (Local Here (File { directory, file })) =
  let adddir = Directory $ (Array.toUnfoldable <<< Array.reverse) $ String.split (String.Pattern "/") (here)
  in Local Here (File { directory: adddir <> directory, file })
moveHere _ i = i

nodeRetrieve :: ImportType -> Aff { result :: String, headers :: Headers }
nodeRetrieve i = case i of
  Missing -> empty
  Env name -> nodeRetrieveEnv name <#> { headers: [], result: _ }
  Local prefix path -> do
    nodeRetrieveFile (prettyFilePrefix prefix <> prettyFile path) <#> { headers: [], result: _ }
  Remote url -> nodeRetrieveURL
    (fromMaybe empty (getHeaders i))
    (prettyURL url)

nodeReadBinary :: String -> Aff ArrayBuffer
nodeReadBinary file =
  Node.FS.Aff.readFile file >>=
    (liftEffect <<< Node.Buffer.toArrayBuffer)

nodeCacheIn :: String ->
  { get :: String -> Aff ArrayBuffer
  , put :: String -> ArrayBuffer -> Aff Unit
  }
nodeCacheIn dir =
  { get: \hash ->
      Node.FS.Aff.readFile (dir <> "/dhall/1220" <> hash) >>=
        (liftEffect <<< Node.Buffer.toArrayBuffer)
  , put: \hash val ->
      Node.FS.Aff.writeFile (dir <> "/dhall/1220" <> hash) =<<
        (liftEffect <<< Node.Buffer.fromArrayBuffer) val
  }

nodeCache ::
  { get :: String -> Aff ArrayBuffer
  , put :: String -> ArrayBuffer -> Aff Unit
  }
nodeCache =
  let
    xdg = lookupEnv "XDG_CACHE_HOME"
    home = lookupEnv "HOME" <#> map (_ <> "/.cache")
    dirs = traverse liftEffect [ xdg, home ]
    onDirs :: forall a. (String -> Aff a) -> Aff a
    onDirs f = dirs >>= (oneOfMap <<< oneOfMap) f
  in
    { get: \hash -> onDirs \dir ->
        Node.FS.Aff.readFile (dir <> "/dhall/1220" <> hash) >>=
          (liftEffect <<< Node.Buffer.toArrayBuffer)
    , put: \hash val -> onDirs \dir ->
        Node.FS.Aff.writeFile (dir <> "/dhall/1220" <> hash) =<<
          (liftEffect <<< Node.Buffer.fromArrayBuffer) val
    }

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

headerType :: forall m a. MapLike String m => AST.Expr m a
headerType = AST.mkRecord $ Dhall.Map.fromFoldable $
  [ Tuple "mapKey" AST.mkText
  , Tuple "mapValue"  AST.mkText
  ]

toHeaders :: forall m a. MapLike String m => AST.Expr m a -> Maybe Headers
toHeaders = AST.projectW >>> flip (VariantF.on (_S::S_ "ListLit")) (pure empty)
  \(Product (Tuple _ items)) -> traverse toHeader items

toHeader :: forall m a. MapLike String m => AST.Expr m a -> Maybe Header
toHeader = AST.projectW >>> flip (VariantF.on (_S::S_ "RecordLit")) (pure empty)
  \m ->
    let
      getLit = AST.projectW >>> flip (VariantF.on (_S::S_ "TextLit")) (pure empty)
        case _ of
          AST.TextLit s -> pure s
          _ -> empty
    in { header: _, value: _ }
      <$> (getLit =<< Dhall.Map.get "mapKey" m)
      <*> (getLit =<< Dhall.Map.get "mapValue" m)

fromHeaders :: forall m a. MapLike String m => Headers -> AST.Expr m a
fromHeaders [] = AST.mkListLit (Just headerType) []
fromHeaders headers = AST.mkListLit Nothing $ fromHeader <$> headers

fromHeader :: forall m a. MapLike String m => Header -> AST.Expr m a
fromHeader { header, value } = AST.mkRecordLit $ Dhall.Map.fromFoldable
  [ Tuple "mapKey" $ AST.mkTextLit' header
  , Tuple "mapValue" $ AST.mkTextLit' value
  ]

appendHeader :: forall m a. MapLike String m => AST.Expr m a -> AST.Expr m a -> AST.Expr m a
appendHeader a b
  | Just { values: x } <- Lens.preview AST._ListLit (AST.projectW a)
  , Just { values: y } <- Lens.preview AST._ListLit (AST.projectW b) =
    let xy = x <> y in
    case xy of
      [] -> AST.mkListLit (Just headerType) []
      _ -> AST.mkListLit Nothing xy
appendHeader a b = AST.mkListAppend a b

desugarHeaders :: forall m. MapLike String m => AST.Expr m Import -> AST.Expr m Import
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

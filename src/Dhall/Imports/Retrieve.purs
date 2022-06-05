module Dhall.Imports.Retrieve where

import Prelude

import Control.Plus (empty)
import Control.Promise (Promise, toAffE)
import Data.Array as Array
import Data.ArrayBuffer.Types (ArrayBuffer)
import Data.Foldable (oneOfMap)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Dhall.Core.Imports (Directory(..), File(..), FilePrefix(..), Headers, ImportType(..), getHeaders, prettyFile, prettyFilePrefix, prettyURL)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Foreign.Object as Foreign.Object
import Node.Buffer as Node.Buffer
import Node.FS.Aff as Node.FS.Aff
import Yoga.Fetch as M
import Yoga.Fetch.Impl (FetchImpl)

foreign import getEnv :: Effect (Foreign.Object.Object String)
foreign import unsafeDecode :: forall r. (String -> r) -> r -> ArrayBuffer -> r

decode :: ArrayBuffer -> Maybe String
decode = unsafeDecode Just Nothing

lookupEnv :: String -> Effect (Maybe String)
lookupEnv k = Foreign.Object.lookup k <$> getEnv

nodeRetrieveEnv :: String -> Aff String
nodeRetrieveEnv name = liftEffect $ lookupEnv name >>= case _ of
  Nothing -> throw $ "Unknown envionment variable: " <> name
  Just v -> pure v

nodeRetrieveFile :: String -> Aff (Maybe String)
nodeRetrieveFile path = nodeReadBinary path <#> decode

foreign import responseHeaders :: M.Response -> M.Headers
foreign import nodeFetch :: Effect (Promise FetchImpl)
foreign import windowFetch :: Unit -> FetchImpl

milkisRetrieveURL :: FetchImpl -> Headers -> String -> Aff { result :: Maybe String, headers :: Headers }
milkisRetrieveURL impl headers = M.URL >>> (=<<) infos <<< flip (M.fetch impl)
  { method: M.getMethod
  -- FIXME: duplicate headers
  , headers: Foreign.Object.fromFoldable
      (headers <#> \{ header, value } -> Tuple header value)
  } where
    infos resp = do
      result <- decode <$> M.arrayBuffer resp
      let resHeaders = Foreign.Object.toUnfoldable (responseHeaders resp) <#>
            \(Tuple header value) -> { header, value }
      pure { result, headers: resHeaders }

nodeRetrieveURL :: Headers -> String -> Aff { result :: Maybe String, headers :: Headers }
nodeRetrieveURL headers url = do
  nodeFetched <- toAffE nodeFetch
  milkisRetrieveURL nodeFetched headers url

windowRetrieveURL :: Headers -> String -> Aff { result :: Maybe String, headers :: Headers }
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

nodeRetrieve :: ImportType -> Aff { result :: Maybe String, headers :: Headers }
nodeRetrieve i = case i of
  Missing -> empty
  Env name -> nodeRetrieveEnv name <#> Just >>> { headers: [], result: _ }
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

nodeHeadersLocation :: Aff String
nodeHeadersLocation = oneOfMap identity
  [ (liftEffect (lookupEnv "XDG_CONFIG_HOME") >>= oneOfMap pure) <#> (_ <> "/dhall/headers.dhall")
  , (liftEffect (lookupEnv "HOME") >>= oneOfMap pure) <#> (_ <> "/.config/dhall/headers.dhall")
  ]

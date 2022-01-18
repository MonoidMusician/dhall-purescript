module Dhall.CLI.Main where

import Prelude

import Data.Array (intercalate)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (for_, traverse_)
import Data.FoldableWithIndex (foldMapWithIndex, forWithIndex_)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap, wrap)
import Data.String as String
import Data.Traversable (traverse)
import Data.TraversableWithIndex (forWithIndex)
import Data.Tuple (Tuple(..), fst)
import Data.Variant (Variant)
import Dhall.Context as Dhall.Context
import Dhall.Core (Pair(..))
import Dhall.Core as Dhall
import Dhall.Core.CBOR (decode)
import Dhall.Imports.Hash as Hash
import Dhall.Imports.Headers as Headers
import Dhall.Imports.Resolve (ImportExpr)
import Dhall.Imports.Resolve as Resolve
import Dhall.Imports.Retrieve as Retrieve
import Dhall.Lib.CBOR as CBOR
import Dhall.Lib.MonoidalState (unStatePart)
import Dhall.Lib.MonoidalState as V
import Dhall.Parser as Parser
import Dhall.Printer as Printer
import Dhall.TypeCheck as TC
import Dhall.TypeCheck.UniSolver (exemplify)
import Effect (Effect)
import Effect.Aff (Aff, launchAff_)
import Effect.Class (liftEffect)
import Effect.Class.Console (log, logShow)
import Node.Process as Process
import Validation.These as VV

single :: forall a. String -> (a -> Aff Unit) -> Array a -> Aff Unit
single thing fn argv = case argv of
  [ s ] -> fn s
  _ -> log ("Specify a single " <> thing)

resolver :: Dhall.ImportType -> Resolve.R
resolver target =
  { stack: pure $ Resolve.Localized $ Dhall.Import
      { importMode: Dhall.Code, importType: target }
  , retriever: Retrieve.nodeRetrieve
  , cacher: Retrieve.nodeCache
  }

print :: forall i. (i -> String) -> Dhall.Expr Dhall.InsOrdStrMap i -> String
print i = Printer.printAST
  { ascii: true
  , printImport: i
  , line: Just (wrap 150)
  , tabs: { width: wrap 2, soft: true, align: false }
  }

normalizeFile :: String -> Aff Unit
normalizeFile file = do
  let target = Dhall.parseImportType file
  text <- Retrieve.nodeRetrieve target <#> _.result
  case Parser.parse =<< text of
    Nothing -> logShow "Parser error"
    Just parsed -> do
      originHeaders <- Headers.originHeadersFromLocationAff Retrieve.nodeHeadersLocation
      Resolve.runM (resolver target) { cache: Map.empty, toBeCached: mempty, originHeaders } (Resolve.resolveImportsHere parsed) >>=
        fst >>> case _ of
          V.Error es _ _ -> do
            logShow "Imports failed"
            for_ es $ traverse \(Tuple _ tag) -> logShow (tag :: Variant (Resolve.Errors ()))
          V.Success _ resolved -> do
            -- logShow resolved
            case TC.withTypeWithA' absurd Dhall.Context.empty resolved of
              VV.Error es _ -> do
                logShow "Type error"
                for_ es \(Tuple _ tag) -> logShow (tag :: Variant (Resolve.Errors ()))
              VV.Success (Tuple st (Pair exp typ)) -> do
                log $ print show typ
                if Map.isEmpty (unwrap st) then mempty else do
                  forWithIndex_ (unwrap st) \k (Tuple _ v) ->
                    log $ show k <> " !>= " <> show v
                  case exemplify st of
                    Left _ -> mempty
                    Right ex ->
                      log $ "e.g. " <> intercalate ", " (ex # foldMapWithIndex \k v -> [k <> " = " <> show v])
                  log mempty
                let normalized = Dhall.normalize exp
                log $ print show normalized
                pure unit

deCBOR :: String -> Aff Unit
deCBOR hash = do
  cached <- Retrieve.nodeCache.get hash
  case decode (CBOR.decode cached) of
    Nothing -> logShow "decoding error"
    Just decoded -> do
      log $ print show decoded
      case traverse (pure Nothing) decoded of
        Nothing -> log "Unexpected imports"
        Just noImports ->
          when (hash /= Hash.hash ((absurd <$> Hash.neutralize noImports) :: ImportExpr)) do
            log "Invalid hash after all"

main :: Effect Unit
main = do
  argv <- Array.drop 2 <$> liftEffect Process.argv
  case Array.head argv >>= flip Map.lookup commands of
    Just cmd ->
      launchAff_ (cmd (Array.drop 1 argv))
    _ -> log $ "Please enter a valid command: " <>
      String.joinWith ", " (Array.fromFoldable (Map.keys commands))

commands :: Map String (Array String -> Aff Unit)
commands = Map.fromFoldable
  [ Tuple "normalize" (single "file to normalize" normalizeFile)
  , Tuple "normalize-all" (traverse_ ((*>) <$> log <*> normalizeFile))
  , Tuple "decode" (single "hash to decode from cache" deCBOR)
  ]

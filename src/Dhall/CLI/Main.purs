module Dhall.CLI.Main where

import Prelude

import Data.Array as Array
import Data.Foldable (for_, traverse_)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap, wrap)
import Data.String as String
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..), fst)
import Data.Variant (Variant)
import Dhall.Core as Dhall
import Dhall.Core.CBOR (decode)
import Dhall.Imports.Hash as Hash
import Dhall.Imports.Resolve (ImportExpr)
import Dhall.Imports.Resolve as Resolve
import Dhall.Imports.Retrieve as Retrieve
import Dhall.Lib.CBOR as CBOR
import Dhall.Parser as Parser
import Dhall.Printer as Printer
import Dhall.TypeCheck as TC
import Effect (Effect)
import Effect.Aff (Aff, launchAff_)
import Effect.Class (liftEffect)
import Effect.Class.Console (log, logShow)
import Node.Process as Process
import Validation.These as V

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
    Just parsed ->
      Resolve.runM (resolver target) { cache: Map.empty, toBeCached: mempty } (Resolve.resolveImportsHere parsed) >>=
        fst >>> unwrap >>> map fst >>> case _ of
          V.Error es _ -> do
            logShow "Imports failed"
            for_ es \(TC.TypeCheckError { tag }) -> logShow (tag :: Variant (Resolve.Errors ()))
          V.Success resolved -> do
            -- logShow resolved
            case TC.typeOf resolved of
              V.Error es _ -> do
                logShow "Type error"
                for_ es \(TC.TypeCheckError { tag }) -> logShow (tag :: Variant (Resolve.Errors ()))
              V.Success a -> do
                log $ print show a
                let normalized = Dhall.normalize resolved
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

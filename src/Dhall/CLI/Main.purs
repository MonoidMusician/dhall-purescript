module Dhall.CLI.Main where

import Prelude

import Data.Array as Array
import Data.Foldable (for_, traverse_)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap, wrap)
import Data.String as String
import Data.Tuple (Tuple(..), fst)
import Data.Variant (Variant)
import Dhall.Core as Dhall
import Dhall.Imports.Resolve as Resolve
import Dhall.Imports.Retrieve as Retrieve
import Dhall.Parser as Parser
import Dhall.Printer as Printer
import Dhall.TypeCheck as TC
import Effect (Effect)
import Effect.Aff (Aff, launchAff_)
import Effect.Class (liftEffect)
import Effect.Class.Console (log, logShow)
import Node.Process as Process
import Validation.These as V

runNormalize :: Array String -> Aff Unit
runNormalize argv = case argv of
  [ s ] -> normalizeFile s
  _ -> log "Specify a single file to normalize"

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
  case Parser.parse text of
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
                -- logShow a
                let normalized = Dhall.normalize resolved
                log $ print show normalized
                pure unit

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
  [ Tuple "normalize" runNormalize
  , Tuple "normalize-all" (traverse_ ((*>) <$> log <*> normalizeFile))
  ]

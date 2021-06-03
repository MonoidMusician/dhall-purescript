module Dhall.CLI.Main where

import Prelude
import Control.Comonad (extract)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (traverse_)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), isJust)
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

resolver :: Resolve.R
resolver =
  { stack: mempty
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
  text <-
    if isJust (String.stripPrefix (String.Pattern "http://") file) || isJust (String.stripPrefix (String.Pattern "https://") file)
      then Retrieve.nodeRetrieveURL mempty file <#> _.result
      else Retrieve.nodeRetrieveFile file
  case Parser.parse text of
    Nothing -> logShow "Parser error"
    Just parsed ->
      Resolve.runM resolver mempty (Resolve.resolveImportsHere parsed) >>=
        fst >>> unwrap >>> map fst >>> case _ of
          V.Error _ _ -> logShow "Imports failed"
          V.Success resolved -> do
            -- logShow resolved
            case TC.typeOf resolved of
              V.Error _ _ -> logShow "Type error"
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

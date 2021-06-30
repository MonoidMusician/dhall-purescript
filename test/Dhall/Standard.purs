module Dhall.Test.Standard where

import Prelude

import Control.Comonad (extract)
import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Control.Monad.Writer (WriterT(..))
import Data.Array as Array
import Data.ArrayBuffer.Types (ArrayBuffer)
import Data.Either (Either(..))
import Data.Foldable (foldMap, traverse_)
import Data.FoldableWithIndex (forWithIndex_)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, isJust)
import Data.Newtype (unwrap, wrap)
import Data.String (Pattern(..), stripSuffix)
import Data.String as String
import Data.Tuple (Tuple(..), fst)
import Data.Variant (Variant)
import Dhall.Core (Directory(..), File(..), FilePrefix(..), Import(..), ImportMode(..), ImportType(..), alphaNormalize, conv, unordered)
import Dhall.Core.CBOR (decode)
import Dhall.Imports.Resolve as Resolve
import Dhall.Imports.Retrieve (nodeCache, nodeReadBinary, nodeRetrieve, nodeRetrieveFile)
import Dhall.Lib.CBOR as CBOR
import Dhall.Map (InsOrdStrMap)
import Dhall.Test (Actions)
import Dhall.Test as Test
import Dhall.Test.Util (eqArrayBuffer)
import Dhall.Test.Util as Util
import Dhall.TypeCheck as TC
import Effect (Effect)
import Effect.Aff (Aff, catchError, error, launchAff_, makeAff, message, throwError)
import Effect.Exception (stack)
import Effect.Aff.Class (liftAff)
import Effect.Class (liftEffect)
import Effect.Class.Console (log, logShow)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Node.Buffer as Buffer
import Node.ChildProcess as ChildProcess
import Node.Encoding (Encoding(..))
import Node.Path (FilePath)
import Node.Process as Process
import Node.Stream as Stream
import Validation.These as V

root = "./dhall-lang/tests/" :: String

note :: String -> Maybe ~> Aff
note msg Nothing = throwError (error (msg))
note _ (Just a) = pure a

noteFb :: forall w e a. Show (Variant e) =>
  String -> TC.Feedback w e InsOrdStrMap a ~> Aff
noteFb msg (WriterT (V.Error es _)) =
  throwError (error (msg <> foldMap (\(TC.TypeCheckError { tag }) -> "\n    " <> show tag) es))
noteFb _ (WriterT (V.Success (Tuple a _))) = pure a

etonFb :: forall w e a b.
  String -> TC.Feedback w e InsOrdStrMap a b -> Aff Unit
etonFb _ (WriterT (V.Error es _)) = pure unit
etonFb msg (WriterT (V.Success (Tuple a _))) = throwError (error msg)

noteR :: forall e a. Show (Variant e) =>
  String -> TC.Result e InsOrdStrMap a ~> Aff
noteR msg (V.Error es _) =
  throwError (error (msg <> foldMap (\(TC.TypeCheckError { tag }) -> "\n    " <> show tag) es))
noteR _ (V.Success a) = pure a

etonR :: forall e a b.
  String -> TC.Result e InsOrdStrMap a b -> Aff Unit
etonR _ (V.Error es _) = pure unit
etonR msg (V.Success a) = throwError (error msg)

type R =
  { filter :: String -> String -> Maybe Boolean
  , results :: Ref (Map String Int)
  }
type RT = ReaderT R Aff

logErrorWith :: RT Unit -> RT Unit -> RT Unit
logErrorWith desc = catchError <@> \err ->
  desc *> log ("  " <> message err) *> case stack err of
    Nothing -> pure unit
    Just e -> pure unit -- log e

testType :: String -> (Boolean -> FilePath -> Aff Unit) -> (Boolean -> FilePath -> Aff Unit) -> RT Unit
testType ty = testType' ty ".dhall"

testType' :: String -> String -> (Boolean -> FilePath -> Aff Unit) -> (Boolean -> FilePath -> Aff Unit) -> RT Unit
testType' section suff success failure = do
  { filter, results } <- ask
  let
    incr :: Ref Int -> RT Unit
    incr c = liftEffect $ Ref.modify_ (_ + 1) c
  successes <- liftAff $ Util.discover2 ("A" <> suff) (root <> section <> "/success") <#>
    Array.mapMaybe (\file -> Tuple <$> filter section file <@> file)
  count0 <- liftEffect $ Ref.new 0
  traverse_ (\(Tuple verb file) -> logErrorWith (log file) (liftAff (success verb file) *> incr count0)) successes
  count1 <- liftEffect $ Ref.new 0
  failures <- liftAff $ Util.discover2 suff (root <> section <> "/failure") <#>
    Array.mapMaybe (\file -> Tuple <$> filter section file <@> file)
  traverse_ (\(Tuple verb file) -> logErrorWith (log file) (liftAff (failure verb file) *> incr count1)) failures
  counted0 <- liftEffect $ Ref.read count0
  counted1 <- liftEffect $ Ref.read count1
  let execed = Array.length successes + Array.length failures
  let percent = (100 * (counted0 + counted1)) / execed
  when (execed > 0) do
    liftEffect $ Ref.modify_ (Map.insert section percent) results
    log $ section <> " score: (" <> show counted0 <> " + " <> show counted1 <> ") / (" <>
      (show $ Array.length successes) <> " + " <> (show $ Array.length failures) <> ") = " <> (show percent) <> "%"

mkActions :: String -> String -> String -> Actions
mkActions ty file = Test.mkActions'
  let split = String.split (String.Pattern "/") file in
  { stack: pure $ wrap $ Import
    { importMode: Code
    , importType: Local Here $ File
      { directory: Directory $
          (Array.toUnfoldable <<< Array.reverse) $ Array.dropEnd 1 split
      , file: fromMaybe "" $ Array.last split
      }
    }
  , cacher:
    { get: nodeCache.get -- requires env:XDG_CACHE_HOME="./dhall-lang/tests/import/cache/"
    , put: \_ _ -> pure unit -- prevents writing to cache
    }
  , retriever: nodeRetrieve
  }

logDiag :: ArrayBuffer -> Aff String
logDiag ab = makeAff \cb -> do
  cp <- ChildProcess.spawn "cbor2diag.rb" [] ChildProcess.defaultSpawnOptions
  ChildProcess.onError cp \_ -> cb (Right "")
  let stdout = ChildProcess.stdout cp
  result <- Ref.new mempty
  Stream.onDataString stdout UTF8 \res ->
    Ref.modify_ (_ <> res) result
  ChildProcess.onExit cp \_ -> do
    res <- Ref.read result
    cb (Right res)
  let stdin = ChildProcess.stdin cp
  buffer <- Buffer.fromArrayBuffer ab
  void $ Stream.write stdin buffer (Stream.end stdin mempty)
  pure mempty

test :: RT Unit
test = do
  testType "parser"
    do \verb success -> do
        textA <- nodeRetrieveFile (success <> "A.dhall")
        let actA = mkActions "parser" success textA
        parsedA <- actA.parse # unwrap # extract #
          note "Failed to parse A"
        binB <- nodeReadBinary (success <> "B.dhallb")
        when ((extract parsedA.encoded).cbor `not eqArrayBuffer` binB) do
          when verb do
            logShow parsedA.parsed
            let binA = (extract parsedA.encoded).cbor
            d1 <- logDiag binA
            d2 <- logDiag binB
            if d1 /= "" && d2 /= "" && d1 /= d2
              then log d1 *> log d2
              else log (Util.showCBOR binA) *> log (Util.showCBOR binB)
          throwError (error "Binary did not match")
    do \verb failure -> do
        text <- nodeRetrieveFile (failure <> ".dhall")
        let act = mkActions "parser" failure text
        let parsed = act.parse # unwrap # extract
        when (isJust parsed) do
          throwError (error "Was not supposed to parse")
  testType "normalization"
    do \verb success -> do
        textA <- nodeRetrieveFile (success <> "A.dhall")
        let actA = mkActions "normalization" success textA
        parsedA <- actA.parse # unwrap # extract #
          note "Failed to parse A"
        importedA <- parsedA.imports # unwrap # extract # unwrap >>=
          noteFb "Failed to resolve A"
        textB <- nodeRetrieveFile (success <> "B.dhall")
        let actB = mkActions "normalization" success textB
        parsedB <- actB.parse # unwrap # extract #
          note "Failed to parse B"
        importedB <- parsedB.imports # unwrap # fst # unwrap # extract #
          note "Failed to resolve B"
        let norm = (conv <<< unordered) (extract importedA.unsafeNormalized)
        when (norm /= importedB.resolved) do
          when verb do
            logShow $ norm
            logShow $ importedB.resolved
          throwError $ error $
            if norm == importedA.resolved
              then "Did not normalize"
              else "Normalization did not match"
    do \verb failure ->
        throwError (error "Why is there a normalization failure?")
  testType "alpha-normalization"
    do \verb success -> do
        textA <- nodeRetrieveFile (success <> "A.dhall")
        let actA = mkActions "alpha-normalization" success textA
        parsedA <- actA.parse # unwrap # extract #
          note "Failed to parse A"
        textB <- nodeRetrieveFile (success <> "B.dhall")
        let actB = mkActions "alpha-normalization" success textB
        parsedB <- actB.parse # unwrap # extract #
          note "Failed to parse B"
        when (alphaNormalize parsedA.parsed /= parsedB.parsed) do
          throwError (error "Alpha-normalization did not match")
    do \verb failure ->
        throwError (error "Why is there an alpha-normalization failure?")
  testType "semantic-hash"
    do \verb success -> do
        textA <- nodeRetrieveFile (success <> "A.dhall")
        let actA = mkActions "semantic-hash" success textA
        parsedA <- actA.parse # unwrap # extract #
          note "Failed to parse"
        when verb do log "Parsed: " *> logShow parsedA.parsed
        importedA <- parsedA.imports # unwrap # extract # unwrap >>=
          noteFb "Failed to resolve A"
        when verb do log "Resolved: " *> logShow importedA.resolved
        typecheckedA <- importedA.typechecked # unwrap # extract #
          noteR "Failed to typecheck A"
        -- when verb do log "Typechecked: " *> logShow typecheckedA.inferredType
        -- when verb do log "Normalized: " *> logShow (extract typecheckedA.safeNormalized)
        -- when verb do log "CBOR: " *> logDiag (extract typecheckedA.encoded).cbor
        hashB <- (fromMaybe <*> stripSuffix (Pattern "\n")) <$> nodeRetrieveFile (success <> "B.hash")
        let hashA = "sha256:" <> (extract typecheckedA.encoded).hash
        when (hashA /= hashB) do
          throwError $ error $ "Binary did not match"
            <> "\n    Got: " <> hashA
            <> "\n    Exp: " <> hashB
    do \verb failure ->
        throwError (error "Why is there a semantic hash failure?")
  testType "type-inference"
    do \verb success -> do
        textA <- nodeRetrieveFile (success <> "A.dhall")
        let actA = mkActions "type-inference" success textA
        parsedA <- actA.parse # unwrap # extract #
          note "Failed to parse A"
        importedA <- parsedA.imports # unwrap # extract # unwrap >>=
          noteFb "Failed to resolve A"
        typecheckedA <- importedA.typechecked # unwrap # extract #
          noteR "Failed to typecheck A"
        textB <- nodeRetrieveFile (success <> "B.dhall")
        let actB = mkActions "type-inference" success textB
        parsedB <- actB.parse # unwrap # extract #
          note "Failed to parse B"
        importedB <- parsedB.imports # unwrap # fst # unwrap # extract #
          note "Failed to resolve B"
        let norm = (conv <<< unordered) (extract typecheckedA.normalizedType)
        when (norm /= importedB.resolved) do
          when true do
            logShow $ norm
            logShow importedB.resolved
          throwError (error "Type inference did not match")
    do \verb failure -> do
        text <- nodeRetrieveFile (failure <> ".dhall")
        let act = mkActions "typecheck" failure text
        parsed <- act.parse # unwrap # extract #
          note "Failed to parse"
        imported <- parsed.imports # unwrap # extract # unwrap >>=
          noteFb "Failed to resolve"
        imported.typechecked # unwrap # extract #
          etonR "Was not supposed to typecheck"
  testType "import"
    do \verb success -> do
        textA <- nodeRetrieveFile (success <> "A.dhall")
        let actA = mkActions "import" success textA
        parsedA <- actA.parse # unwrap # extract #
          note "Failed to parse A"
        importedA <- parsedA.imports # unwrap # extract # unwrap >>=
          noteFb "Failed to resolve A"
        textB <- nodeRetrieveFile (success <> "B.dhall")
        let actB = mkActions "import" success textB
        parsedB <- actB.parse # unwrap # extract #
          note "Failed to parse B"
        importedB <- parsedB.imports # unwrap # fst # unwrap # extract #
          note "Failed to resolve B"
        when (unordered importedA.resolved /= unordered importedB.resolved) do
          when (true || verb) do
            logShow importedA.resolved
            logShow importedB.resolved
          throwError (error "Imports did not match")
    do \verb failure -> do
        text <- nodeRetrieveFile (failure <> ".dhall")
        let act = mkActions "import" failure text
        parsed <- act.parse # unwrap # extract #
          note "Failed to parse"
        void $ parsed.imports # unwrap # extract # unwrap >>=
          etonFb "Was not supposed to import correctly"
  testType' "binary-decode" ".dhallb"
    do \verb success -> do
        binA <- nodeReadBinary (success <> "A.dhallb")
        decodedA <- binA # CBOR.decode # decode #
          note "Failed to decode A"
        textB <- nodeRetrieveFile (success <> "B.dhall")
        let actB = mkActions "binary-decode" success textB
        parsedB <- actB.parse # unwrap # extract #
          note "Failed to parse B"
        when (decodedA /= parsedB.parsed) do
          when verb do
            logShow decodedA
            logShow parsedB.parsed
          throwError (error "Expressions did not match")
    do \verb failure -> do
        bin <- nodeReadBinary (failure <> ".dhallb")
        let decoded = (bin # CBOR.decode # decode) :: Maybe Resolve.ImportExpr
        when (isJust decoded) do
          throwError (error "Was not supposed to decode")

main :: Effect Unit
main = launchAff_ do
  argv <- Array.drop 2 <$> liftEffect Process.argv
  let
    { no: sections_, yes: files_ } =
      Array.partition (String.contains (String.Pattern "/")) argv
    separate as =
      { yes: Array.filter (not Util.startsWith <@> "-") as
      , no: Array.mapMaybe (Util.startingWith <@> "-") as
      }
    sections = separate sections_
    files = separate files_
    filter :: String -> String -> Maybe Boolean
    filter section file =
      let
        allowed = Array.elem section sections.yes || Array.elem file files.yes ||
          (Array.null sections.yes && Array.null files.yes)
        rejected = Array.elem section sections.no || Array.elem file files.no
      in if allowed && not rejected
        then Just (Array.elem file files.yes)
        else Nothing
  results <- liftEffect $ Ref.new Map.empty
  runReaderT test { filter, results }
  finalResults <- liftEffect $ Ref.read results
  if finalResults == Map.empty
    then log "No tests run"
    else
      forWithIndex_ finalResults \k v ->
        log $ k <> ": " <> show v <> "%"

module Dhall.Test.Standard where

import Prelude

import Control.Alternative (empty, guard, (<|>))
import Control.Comonad (extract)
import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Control.Monad.Writer (WriterT(..))
import Data.Array as Array
import Data.ArrayBuffer.Types (ArrayBuffer)
import Data.Either (Either(..))
import Data.Foldable (foldMap, for_, oneOfMap, traverse_)
import Data.FoldableWithIndex (forWithIndex_)
import Data.Lens (preview)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, isJust)
import Data.Newtype (unwrap, wrap)
import Data.String (Pattern(..), stripSuffix)
import Data.String as String
import Data.Traversable (traverse)
import Data.TraversableWithIndex (traverseWithIndex)
import Data.Tuple (Tuple(..), fst)
import Data.Variant (Variant)
import Dhall.Core (Directory(..), File(..), FilePrefix(..), Import(..), ImportMode(..), ImportType(..), alphaNormalize, conv, projectW, unordered)
import Dhall.Core as AST
import Dhall.Core.CBOR (encode, decode)
import Dhall.Imports.Resolve as Resolve
import Dhall.Imports.Retrieve (nodeCache, nodeReadBinary, nodeRetrieve, nodeRetrieveFile)
import Dhall.Lib.CBOR as CBOR
import Dhall.Map (InsOrdStrMap)
import Dhall.Map as Dhall.Map
import Dhall.Test (Actions, parse, print)
import Dhall.Test as Test
import Dhall.Test.Util (eqArrayBuffer)
import Dhall.Test.Util as Util
import Dhall.TypeCheck as TC
import Effect (Effect)
import Effect.Aff (Aff, catchError, error, launchAff_, makeAff, message, throwError)
import Effect.Aff.Class (liftAff)
import Effect.Class (liftEffect)
import Effect.Class.Console (log, logShow)
import Effect.Exception (stack)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Matryoshka (project)
import Node.Buffer as Buffer
import Node.ChildProcess as ChildProcess
import Node.Encoding (Encoding(..))
import Node.Path (FilePath)
import Node.Process as Process
import Node.Stream as Stream
import Unsafe.Coerce (unsafeCoerce)
import Dhall.Lib.MonoidalState as V
import Validation.These as VV

root = "./dhall-lang/tests/" :: String

note :: String -> Maybe ~> Aff
note msg Nothing = throwError (error (msg))
note _ (Just a) = pure a

noteFb :: forall w e a. Show (Variant e) =>
  String -> TC.Feedback w e InsOrdStrMap a ~> Aff
noteFb msg (V.Error es _ _) =
  throwError (error (msg <> foldMap (foldMap \(Tuple _ tag) -> "\n    " <> show tag) es))
noteFb _ (V.Success _ a) = pure a

etonFb :: forall w e a b.
  String -> TC.Feedback w e InsOrdStrMap a b -> Aff Unit
etonFb _ (V.Error _ _ _) = pure unit
etonFb msg (V.Success _ _) = throwError (error msg)

noteR :: forall e a. Show (Variant e) =>
  String -> TC.Result e InsOrdStrMap a ~> Aff
noteR msg (VV.Error es _) =
  throwError (error (msg <> foldMap (\(Tuple _ tag) -> "\n    " <> show tag) es))
noteR _ (VV.Success a) = pure a

etonR :: forall e a b.
  String -> TC.Result e InsOrdStrMap a b -> Aff Unit
etonR _ (VV.Error _ _) = pure unit
etonR msg (VV.Success _) = throwError (error msg)

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
  , retriever:
      let
        retrieveSpecial (Env name) = do
          contents <- nodeRetrieveFile (file <> "ENV.dhall") >>= note (file <> "ENV.dhall had no contents")
          parsed <- Test.parse contents >>= Test.noImports # note (file <> "ENV.dhall did not parse")
          let
            goalType = AST.mkApp AST.mkList (AST.mkRecord (Dhall.Map.fromFoldable
              [ Tuple "mapKey" AST.mkText, Tuple "mapValue" AST.mkText ]
            ))
          void $ Test.tc (AST.mkAnnot parsed goalType) # note (file <> "ENV.dhall did not typecheck")
          note (file <> " did not have key") do
            list <- preview AST._ListLit (projectW (Test.normalize parsed)) <#> _.values
            list # oneOfMap \item -> do
              textValues <- preview AST._RecordLit $ projectW item
              strValues <- traverse (preview AST._TextLit_single <<< projectW) textValues
              guard $ Dhall.Map.get "mapKey" strValues == Just name
              Dhall.Map.get "mapValue" strValues <#> Just >>> { headers: [], result: _ }
        retrieveSpecial _ = empty
      in \i -> retrieveSpecial i <|> nodeRetrieve i
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
  seen <- liftEffect $ Ref.new (Map.empty :: Map String Resolve.ImportExpr)
  let
    see :: String -> Resolve.ImportExpr -> Aff Unit
    see k v = liftEffect $ Ref.modify_ (Map.insert k v) seen
  testType "parser"
    do \verb success -> do
        textA <- nodeRetrieveFile (success <> "A.dhall") >>= note "Failed to decode A"
        let actA = mkActions "parser" success textA
        parsedA <- actA.parse # unwrap # extract #
          note "Failed to parse A"
        see (success <> "A.dhall") parsedA.parsed
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
        let decodedB = decode (CBOR.decode binB)
        when (decodedB /= Just (unordered parsedA.parsed)) do
          case decodedB of
            Nothing -> do
              log $ unsafeCoerce $ CBOR.decode binB
              throwError (error "Could not decode B")
            Just decoded -> do
              logShow decoded
              logShow parsedA.parsed
              throwError (error "Parsed binary did not match parsed text")
    do \verb failure -> do
        mtext <- nodeRetrieveFile (failure <> ".dhall")
        for_ mtext \text -> do
          let act = mkActions "parser" failure text
          let parsed = act.parse # unwrap # extract
          when (isJust parsed) do
            throwError (error "Was not supposed to parse")
  testType "normalization"
    do \verb success -> do
        textA <- nodeRetrieveFile (success <> "A.dhall") >>= note "Failed to decode A"
        let actA = mkActions "normalization" success textA
        parsedA <- actA.parse # unwrap # extract #
          note "Failed to parse A"
        see (success <> "A.dhall") parsedA.parsed
        importedA <- parsedA.imports # unwrap # extract # unwrap >>=
          noteFb "Failed to resolve A"
        see (success <> "A.dhall.resolved") (map absurd importedA.resolved)
        textB <- nodeRetrieveFile (success <> "B.dhall") >>= note "Failed to decode B"
        let actB = mkActions "normalization" success textB
        parsedB <- actB.parse # unwrap # extract #
          note "Failed to parse B"
        see (success <> "B.dhall") parsedB.parsed
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
        textA <- nodeRetrieveFile (success <> "A.dhall") >>= note "Failed to decode A"
        let actA = mkActions "alpha-normalization" success textA
        parsedA <- actA.parse # unwrap # extract #
          note "Failed to parse A"
        textB <- nodeRetrieveFile (success <> "B.dhall") >>= note "Failed to decode B"
        let actB = mkActions "alpha-normalization" success textB
        parsedB <- actB.parse # unwrap # extract #
          note "Failed to parse B"
        when (alphaNormalize parsedA.parsed /= parsedB.parsed) do
          throwError (error "Alpha-normalization did not match")
    do \verb failure ->
        throwError (error "Why is there an alpha-normalization failure?")
  testType "semantic-hash"
    do \verb success -> do
        textA <- nodeRetrieveFile (success <> "A.dhall") >>= note "Failed to decode A"
        let actA = mkActions "semantic-hash" success textA
        parsedA <- actA.parse # unwrap # extract #
          note "Failed to parse"
        see (success <> "A.dhall") parsedA.parsed
        when verb do log "Parsed: " *> logShow parsedA.parsed
        importedA <- parsedA.imports # unwrap # extract # unwrap >>=
          noteFb "Failed to resolve A"
        see (success <> "A.dhall.resolved") (map absurd importedA.resolved)
        when verb do log "Resolved: " *> logShow importedA.resolved
        typecheckedA <- importedA.typechecked # unwrap # extract #
          noteR "Failed to typecheck A"
        -- when verb do log "Typechecked: " *> logShow typecheckedA.inferredType
        -- when verb do log "Normalized: " *> logShow (extract typecheckedA.safeNormalized)
        -- when verb do log "CBOR: " *> logDiag (extract typecheckedA.encoded).cbor
        see (success <> "A.dhall.type") (map absurd typecheckedA.inferredType)
        hashB <- (fromMaybe <*> stripSuffix (Pattern "\n")) <$> (nodeRetrieveFile (success <> "B.hash") >>= note "Failed to decode B")
        let hashA = "sha256:" <> (extract typecheckedA.encoded).hash
        when (hashA /= hashB) do
          throwError $ error $ "Binary did not match"
            <> "\n    Got: " <> hashA
            <> "\n    Exp: " <> hashB
    do \verb failure ->
        throwError (error "Why is there a semantic hash failure?")
  testType "type-inference"
    do \verb success -> do
        textA <- nodeRetrieveFile (success <> "A.dhall") >>= note "Failed to decode A"
        let actA = mkActions "type-inference" success textA
        parsedA <- actA.parse # unwrap # extract #
          note "Failed to parse A"
        see (success <> "A.dhall") parsedA.parsed
        importedA <- parsedA.imports # unwrap # extract # unwrap >>=
          noteFb "Failed to resolve A"
        see (success <> "A.dhall.resolved") (map absurd importedA.resolved)
        typecheckedA <- importedA.typechecked # unwrap # extract #
          noteR "Failed to typecheck A"
        see (success <> "A.dhall.type") (map absurd typecheckedA.inferredType)
        textB <- nodeRetrieveFile (success <> "B.dhall") >>= note "Failed to decode B"
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
        text <- nodeRetrieveFile (failure <> ".dhall") >>= note "Failed to decode"
        let act = mkActions "typecheck" failure text
        parsed <- act.parse # unwrap # extract #
          note "Failed to parse"
        see (failure <> ".dhall") parsed.parsed
        imported <- parsed.imports # unwrap # extract # unwrap >>=
          noteFb "Failed to resolve"
        imported.typechecked # unwrap # extract #
          etonR "Was not supposed to typecheck"
  testType "import"
    do \verb success -> do
        textA <- nodeRetrieveFile (success <> "A.dhall") >>= note "Failed to decode A"
        let actA = mkActions "import" success textA
        parsedA <- actA.parse # unwrap # extract #
          note "Failed to parse A"
        importedA <- parsedA.imports # unwrap # extract # unwrap >>=
          noteFb "Failed to resolve A"
        textB <- nodeRetrieveFile (success <> "B.dhall") >>= note "Failed to decode B"
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
        text <- nodeRetrieveFile (failure <> ".dhall") >>= note "Failed to decode"
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
        textB <- nodeRetrieveFile (success <> "B.dhall") >>= note "Failed to decode B"
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
  do
    didSee <- liftEffect (Ref.read seen)
    results <- didSee # traverseWithIndex \src expr ->
      let printed = print expr
      in case parse printed of
        Just e | e == expr -> pure true
        Nothing -> do
          log $ "Failed to reparse " <> src
          log $ "Result: " <> show printed
          log printed
          pure false
        Just e -> do
          log $ "Failed to roundtrip on " <> src
          log $ printed
          log $ "Got this: " <> show e
          log $ "Instead of: " <> show expr
          pure false
    let failed = Array.length (Array.filter (_ == false) (Array.fromFoldable results))
    when (failed > 0) do
      log $ "Total printing failures: " <> show failed
    pure unit

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
        rejected = Array.elem section sections.no || Array.elem file files.no ||
          isJust (String.stripSuffix (String.Pattern "ENV") file)
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

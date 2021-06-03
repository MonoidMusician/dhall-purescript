module Dhall.Imports.Resolve where

import Prelude

import Control.Alt ((<|>))
import Control.Apply (lift2)
import Control.Monad.Reader (ReaderT(..))
import Control.Monad.Writer (WriterT(..))
import Control.Parallel (parallel, sequential)
import Control.Plus (empty)
import Data.ArrayBuffer.Types (ArrayBuffer)
import Data.Bifunctor (lmap)
import Data.Function (on)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Variant as VariantF
import Data.HeytingAlgebra (implies)
import Data.Lens.Record (prop)
import Data.Lens.Record as Lens
import Data.List (List)
import Data.List as List
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), isJust)
import Data.Newtype (class Newtype, un, unwrap)
import Data.Set (Set)
import Data.Set as Set
import Data.String as String
import Data.Traversable (sequence, traverse, traverse_)
import Data.Tuple (Tuple(..))
import Data.Variant (Variant)
import Data.Variant as Variant
import Dhall.Core (Expr, Headers, Import(..), ImportMode(..), ImportType(..), Pair(..), S_, URL(..), _S, normalize, rewriteTopDownA)
import Dhall.Core as AST
import Dhall.Core.AST.Operations (rewriteBottomUpA')
import Dhall.Core.CBOR (decode, encode)
import Dhall.Core.Imports (addHeaders, canonicalizeImport, getHeader, isLocal)
import Dhall.Imports.Hash as Hash
import Dhall.Imports.Retrieve (fromLocation, toHeaders)
import Dhall.Lib.CBOR as CBOR
import Dhall.Map (InsOrdStrMap)
import Dhall.Parser as Parser
import Dhall.TypeCheck (L, typeOf)
import Dhall.TypeCheck as TC
import Effect.AVar (AVar)
import Effect.Aff (Aff)
import Effect.Aff as Aff
import Effect.Aff.AVar as AVar
import Effect.Class (liftEffect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Validation.These as V

newtype Localized = Localized Import
derive instance newtypeLocalized :: Newtype Localized _
derive newtype instance eqLocalized :: Eq Localized
derive newtype instance ordLocalized :: Ord Localized
derive newtype instance showLocalized :: Show Localized

type ImportExpr = Expr InsOrdStrMap Import
type LocalizedExpr = Expr InsOrdStrMap Localized
type ResolvedExpr = Expr InsOrdStrMap Void
type R =
  -- A list of imports visited, in reverse order (i.e. head is the deepest)
  { stack :: List Localized
  -- The function used to retrieve imports
  , retriever :: ImportType -> Aff { result :: String, headers :: Headers }
  -- Get and put expressions from the cache, wherever it is.
  -- May return Aff errors, especially for cache misses, though these are
  -- all silenced.
  , cacher ::
    { get :: String -> Aff ArrayBuffer
    , put :: String -> ArrayBuffer -> Aff Unit
    }
  }
type S =
  -- In-memory cache of imports, both as text and to-be-resolved expressions
  { cache :: Map Localized
    { text :: AVar String
    , resolved :: Maybe (AVar ResolvedExpr)
    }
  -- Set of hashes whose results will be written to cache
  , toBeCached :: Set String
  }
type Infos w =
  -- Keep track of import graph
  ( graph :: { parent :: Localized, child :: Localized }
  | w
  )
type Errors r = TC.Errors
  ( "Parse error" :: Unit
  , "Invalid headers" :: Unit
  , "Import error" :: Aff.Error
  , "Cyclic import" :: Localized
  , "Referentially opaque" :: Localized
  , "Not CORS compliant" ::
    { expectedOrigins :: Array String
    , actualOrigin :: String
    }
  , "Missing import" :: Unit
  , "Hash mismatch" ::
    { expected :: String
    , actual :: String
    }
  , "Import failed to resolve" :: Localized
  | r
  )
type Feedback w r = TC.Feedback (Infos w) (Errors r) InsOrdStrMap Import

-- FIXME: use different location
loc :: L InsOrdStrMap Import
loc = pure $ Tuple empty empty

-- The not-quite-Monad stack that resolution occurs in:
-- - Aff for effects
-- - Reader over R
-- - Aff-State over S
-- - Writer over Array (Variant (Infos w))
-- - Errors over NonEmptyArray (Variant (Errors r))
newtype M w r a = M
  (ReaderT (Tuple R (Ref S)) (N w r) a)
-- Half of M: no ReaderT
type N w r = Compose Aff (Feedback w r)
derive instance newtypeM :: Newtype (M w r a) _
derive newtype instance functorM :: Functor (M w r)
instance applyM :: Apply (M w r) where
  apply (M (ReaderT rf1)) (M (ReaderT rf2)) = M $ ReaderT \rs -> Compose $
    sequential $
      lift2 (<*>) (parallel $ unwrap $ rf1 rs) (parallel $ unwrap $ rf2 rs)
instance applicativeM :: Applicative (M w r) where
  pure = M <<< pure
instance bindM :: Bind (M w r) where
  bind (M (ReaderT rf)) f = M $ ReaderT \rs -> Compose $ map WriterT do
    fa <- map (un WriterT) $ un Compose $ rf rs
    let
      run a = case f a of
        M (ReaderT rf') -> do
          map (un WriterT) $ un Compose $ rf' rs
    case fa of
      V.Success (Tuple a w) ->
        run a <#> case _ of
          V.Success (Tuple b w') -> V.Success (Tuple b (w <> w'))
          V.Error es' mb -> V.Error es' (mb <#> map (append w))
      V.Error es (Just (Tuple a w)) ->
        run a <#> case _ of
          V.Success (Tuple b w') -> V.Success (Tuple b (w <> w'))
          V.Error es' mb -> V.Error (es <> es') (mb <#> map (append w))
      V.Error es Nothing -> pure (V.Error es Nothing)

-- Run the `ReaderT` layer but pause the remaining effects
pause :: forall w r a. M w r a -> M w r (N w r a)
pause (M (ReaderT rf)) = M (ReaderT \r -> pure (rf r))

-- Run the remaining effects
resume :: forall w r. N w r ~> M w r
resume n = M (ReaderT (pure n))

runM :: forall w r a. R -> S -> M w r a -> Aff (Tuple (Feedback w r a) S)
runM r s (M (ReaderT rf)) = do
  ref <- liftEffect (Ref.new s)
  Tuple <$> unwrap (rf (Tuple r ref)) <*> liftEffect (Ref.read ref)

ask :: forall w r. M w r R
ask = M $ ReaderT \(Tuple r _) -> pure r

asks :: forall w r a. (R -> a) -> M w r a
asks = map <@> ask

local :: forall w r. (R -> R) -> M w r ~> M w r
local f (M (ReaderT rf)) = M $ ReaderT \(Tuple r s) -> rf (Tuple (f r) s)

state :: forall w r a. (S -> Tuple a S) -> M w r a
state f = M $ ReaderT \(Tuple r rs) -> Compose do
  s0 <- liftEffect (Ref.read rs)
  let Tuple a s1 = f s0
  liftEffect $ Ref.write s1 rs
  pure $ pure a

get :: forall w r. M w r S
get = state $ join Tuple

gets :: forall w r a. (S -> a) -> M w r a
gets = map <@> get

modify_ :: forall w r. (S -> S) -> M w r Unit
modify_ = state <<< (<<<) (Tuple unit)

tell :: forall w r. Variant (Infos w) -> M w r Unit
tell v = liftFeedback $ WriterT $ pure $ Tuple unit (pure v)

throwFb :: forall w r a. Variant (Errors r) -> Feedback w r a
throwFb e = WriterT $
  V.Error (pure (TC.TypeCheckError { location: loc, tag: e })) Nothing

throw :: forall w r a. Variant (Errors r) -> M w r a
throw e = liftFeedback $ throwFb e

withCleanup :: forall w r a.
  Aff Unit -> M w r a -> M w r a
withCleanup h (M (ReaderT rf)) = M $ ReaderT \r -> Compose $
  unwrap (rf r) >>= \a -> a <$ case a of
    WriterT (V.Error _ _) -> h
    _ -> pure unit

note :: forall w r. Variant (Errors r) -> Maybe ~> M w r
note e = case _ of
  Just a -> pure a
  Nothing -> throw e

rehydrateFeedback :: forall w r a.
  TC.Feedback w r InsOrdStrMap Void ~>
  TC.Feedback w r InsOrdStrMap a
rehydrateFeedback (WriterT f) =
  WriterT ((lmap <<< map <<< map <<< map <<< map <<< map) absurd f)

liftFeedback :: forall w r. Feedback w r ~> M w r
liftFeedback f = M $ ReaderT $ pure $ Compose $ pure f

liftAff :: forall w r. Aff ~> M w r
liftAff f = M $ ReaderT $ pure $ Compose $ pure <$> f

liftAff' :: forall w r a. (Aff.Error -> M w r a) -> Aff a -> M w r a
liftAff' h f = M $ ReaderT \r -> Compose $
  Aff.catchError (pure <$> f) \err ->
    unwrap (unwrap (unwrap (h err)) r)





parent :: forall w r. M w r (Maybe Localized)
parent = asks $ _.stack >>> List.head

-- Localize an import based on its parent, using Semigroup Import
localize :: forall w r. Import -> M w r Localized
localize i =
  parent >>= case _ of
    Nothing -> pure $ Localized <<< canonicalizeImport $ i
    Just p@(Localized i') -> do
      let i'' = Localized <<< canonicalizeImport $ i' <> i
      tell (Variant.inj (_S::S_ "graph") { parent: p, child: i'' })
      pure $ i''

-- Resolve all imports in an expression based on the locale on the stack
resolveImportsHere :: forall w r. ImportExpr -> M w r ResolvedExpr
resolveImportsHere expr = traverse localize expr >>= resolveImports

-- Resolve all imports in an expression
resolveImports :: forall w r. LocalizedExpr -> M w r ResolvedExpr
resolveImports = pure
  -- Caching stage 1: try to load hashed expressions from cache, and mark
  -- cache misses
  >=> replaceCached
  -- Resolve headers so that they are available as PS values
  -- (Eta-expanded because it calls this recursively, of course)
  >=> do \expr -> resolveHeaders expr
  -- Traverse to set up resolving each individual import
  >=> do \expr -> traverse (resolveImport >>> pause) expr
  -- Handle failures in `ImportAlt` expressions, running effects only as necessary
  -- Caching stage 2: check hashes, before `ImportAlt` resolution
  >=> map resume >>> resolveAlternativesAndCheckHashes
  -- Caching stage 3: cache the uncached exprs
  >=> cacheResults

-- Run the effects encoded in the tree, avoiding evaluating second alternatives,
-- except to recover from an error in the first.
-- For hashed expressions, verify that the hash matches and return the
-- normalized node.
-- I wish these did not have to be one step.
resolveAlternativesAndCheckHashes :: forall w r.
  Expr InsOrdStrMap (M w r ResolvedExpr) -> M w r ResolvedExpr
resolveAlternativesAndCheckHashes = rewriteBottomUpA' $ identity
  <<< VariantF.on (_S::S_ "Embed") unwrap -- this is like a `join`
  <<< VariantF.on (_S::S_ "ImportAlt") recover
  <<< VariantF.on (_S::S_ "Hashed") (sequence >=> checkHash)
  where
    checkHash :: Tuple String ResolvedExpr -> M w r ResolvedExpr
    checkHash = \(Tuple hash expr) -> do
      let exprn = Hash.neutralize expr
      let hash' = Hash.hash (absurd <$> exprn :: ImportExpr)
      when (String.toLower hash /= String.toLower hash') do
        throw (Variant.inj (_S::S_ "Hash mismatch") { expected: hash, actual: hash' })
      -- Recurse on the original but return the *normalized* node
      -- See: https://github.com/dhall-lang/dhall-lang/issues/690#issuecomment-518442494
      pure $ AST.mkHashed exprn hash
    isRecoverableError = unwrap >>> _.tag >>> Variant.onMatch
      { "Missing import": const true
      , "Import error": const true
      , "Import failed to resolve": const true
      } (const false)
    recover :: Pair (M w r ResolvedExpr) -> M w r ResolvedExpr
    recover (Pair l r) = M $ ReaderT \rs -> Compose $ WriterT <$> do
      l' <- unwrap <$> unwrap (unwrap (unwrap l) rs)
      case l' of
        V.Error as ma | List.any isRecoverableError as -> do
          r' <- unwrap <$> unwrap (unwrap (unwrap r) rs)
          case r' of
            V.Success a -> pure $ V.Success a
            V.Error bs mb -> pure $ V.Error (as <> bs) (ma <|> mb)
        _ -> pure l'

-- For hashes found in the cache, replace the expression with that
replaceCached :: forall w r. LocalizedExpr -> M w r LocalizedExpr
replaceCached = rewriteTopDownA $ VariantF.on (_S::S_ "Hashed")
  \(Tuple hash expr) -> do
    -- Look up the hash in the cache
    cacher <- asks _.cacher
    fromCache <- liftAff' (pure (pure Nothing)) $ Just <$> cacher.get hash
    Tuple wasCached expr' <- case fromCache of
      Just cached
        -- Note: the hash is verified in stage 2, though a strict reading of the
        -- standard would suggest it should be checked here
        -- TODO: verify expression typechecks and is (alpha-)normalized?
        | Just decoded <- decode (CBOR.decode cached)
        , Just noImports <- traverse (pure Nothing) decoded
        , hash == Hash.hash ((absurd <$> Hash.neutralize noImports) :: ImportExpr) -> do
          let noImports' = absurd <$> noImports
          -- liftAff $ logShow noImports'
          pure $ Tuple true noImports'
      -- Recurse since this was a cache miss, maybe an inner node will succeed
      _ -> Tuple false <$> replaceCached expr
    -- Mark this hash as uncached
    when (not wasCached) do
      modify_ $ prop (_S::S_ "toBeCached") $ Set.insert hash
    -- Return the node, or the one from the cache
    pure $ AST.mkHashed expr' hash

-- For hashed expressions, add to the cache, and return the node without the hash.
cacheResults :: forall w r. ResolvedExpr -> M w r ResolvedExpr
cacheResults = rewriteTopDownA $ VariantF.on (_S::S_ "Hashed")
  \(Tuple hash expr) -> do
    -- Hashes that were not cached need to be put into the cache
    wasCached <- gets $ _.toBeCached >>> not Set.member hash
    when (not wasCached) do
      cacher <- asks _.cacher
      -- Ignore errors when putting it into the cache
      liftAff' (pure (pure unit)) $
        cacher.put hash (CBOR.encode $ encode $ (absurd <$> expr :: ImportExpr))
      -- Make sure not to put this hash twice
      modify_ $ prop (_S::S_ "toBeCached") $ Set.delete hash
    -- Recurse, dropping the hash now
    cacheResults expr

-- Resolve and normalize headers expressions, and match them up with their
-- imports (storing them as PS `Headers` data now, no longer a Dhall expr)
resolveHeaders :: forall w r. LocalizedExpr -> M w r LocalizedExpr
resolveHeaders = rewriteTopDownA $ VariantF.on (_S::S_ "UsingHeaders")
  \(Pair expr headers) -> do
    -- Resolve imports on the headers
    -- Note: the result must be well-typed
    headers' <- resolveImports headers
    -- Normalize them
    let headers'' = normalize headers'
    -- And extract a literal value
    resolved <- toHeaders headers'' #
      note (Variant.inj (_S::S_ "Invalid headers") unit)
    -- Recurse, add inner headers first, then these outer ones
    -- (Note that the UsingHeaders node disappears)
    resolveHeaders expr <#> map
      \(Localized i) -> Localized (addHeaders resolved i)

-- Retrieve an import using the retriever in the Reader context
retrieveImport :: forall w r. ImportType -> M w r { headers :: Headers, result :: String }
retrieveImport Missing = throw (Variant.inj (_S::S_ "Missing import") unit)
retrieveImport i = do
  retriever <- asks _.retriever
  liftAff' (throw <<< Variant.inj (_S::S_ "Import error")) $
    retriever i

parseImport :: forall w r. String -> M w r ImportExpr
parseImport = Parser.parse >>> note (Variant.inj (_S::S_ "Parse error") unit)

-- Ensure the expr typechecks
ensureWellTyped :: forall w r. ResolvedExpr -> M w r ResolvedExpr
ensureWellTyped e = e <$ do
  void $ liftFeedback $ rehydrateFeedback $ V.liftW $
    typeOf e

-- The main workhorse: turn a localized import into a resolved expression
resolveImport :: forall w r. Localized -> M w r ResolvedExpr
resolveImport i@(Localized (Import { importMode, importType })) =
  importType # case importMode, importType of
    Location, _ -> fromLocation >>> pure
    _, Missing -> \_ -> throw (Variant.inj (_S::S_ "Missing import") unit)
    RawText, _ -> referentiallySane >=> retrieveTextVerifiedOrCached Nothing >>> map AST.mkTextLit'
    Code, _ -> checkCycle >=> referentiallySane >=> retrieveExprVerifiedOrCached
  where
    -- Manage imported text in the cache
    -- Takes Maybe AVar indicating intent to resolve as source
    retrieveTextVerifiedOrCached resolver a = do
      cache <- gets _.cache
      case Map.lookup i cache <#> _.text of
        Just retrieving -> do
          -- liftAff $ log $ "Found " <> show i
          when (resolver # isJust) do
            -- Put resolver in state as a courtesy
            modify_ $ prop (_S::S_ "cache") $
              Map.insert i { text: retrieving, resolved: resolver }
          liftAff' (pure (throw (Variant.inj (_S::S_ "Import failed to resolve") i))) $
              AVar.read retrieving
        Nothing -> do
          -- liftAff $ log $ "Caching " <> show i
          retrieving <- liftAff AVar.empty
          modify_ $ prop (_S::S_ "cache") $
            Map.insert i { text: retrieving, resolved: resolver }
          retrieved <- retrieveTextVerified a
          void $ liftAff $ AVar.tryPut retrieved retrieving
          -- liftAff $ log $ "Cached " <> show i
          pure retrieved
    -- Retrieve the import as text over the wire and ensure it is CORS compliant
    retrieveTextVerified = pure
      >=> retrieveImport
      >=> corsCompliant

    -- Manage exprs in the cache
    retrieveExprVerifiedOrCached a = do
      cache <- gets _.cache
      case Map.lookup i cache >>= _.resolved of
        -- Return the cached expression, possibly waiting for it to finish
        -- resolving (in the case of diamond imports, a sibling may wait for the
        -- first thread to complete resolving the shared import)
        Just resolving -> do
          -- liftAff $ log $ "Waiting for " <> show i
          -- TODO: this does not tell us whether it is a recoverable error?
          liftAff' (pure (throw (Variant.inj (_S::S_ "Import failed to resolve") i))) $
            AVar.read resolving
        -- Otherwise, create the resolved value
        Nothing -> do
          -- Make an AVar to hold the result, and pass it while retrieving text
          resolving <- liftAff AVar.empty
          -- Then obtain the text of the import, from cache or retrieved
          -- (this also will put `resolving` in state)
          text <- retrieveTextVerifiedOrCached (Just resolving) a
          -- Fully parse, resolve, and verify the import
          resolved <- retrieveExprVerified text #
            withCleanup (AVar.kill (Aff.error $ "Import failed " <> show i) resolving)
          -- And stick it in the AVar, both for any listeners that popped up
          -- in parallel, and for future reference
          -- NOTE: this may be called even if the AVar is killed, because of the
          -- error-recovering semantics of V.Erroring
          void $ liftAff $ AVar.tryPut resolved resolving
          -- And return it, of course
          pure resolved
    -- Verify an imported expr
    retrieveExprVerified = pure
      -- Parse it
      >=> parseImport
      -- Localize and recursively resolve imports
      >=> recurse
      -- Ensure it typechecks
      >=> ensureWellTyped
      >>> map normalize
    -- Recurse, pushing context onto the stack and resolving all the imports
    -- based on that locale
    recurse = local (Lens.prop (_S::S_ "stack") (List.Cons i)) <<<
      resolveImportsHere

    -- Make sure this import is not trying to import itself
    checkCycle a = a <$ do
      stack <- asks _.stack
      if List.elem i stack
        then throw (Variant.inj (_S::S_ "Cyclic import") i)
        else pure unit
    -- Ensure the import is referentially sane
    referentiallySane a = a <$ do
      parent >>= traverse_
        \(Localized (Import { importType: parentType })) ->
          if isLocal importType `implies` isLocal parentType
            then pure unit
            else throw (Variant.inj (_S::S_ "Referentially opaque") i)

    -- CORS compliance checks
    toOrigin url = show url.scheme <> "://" <> url.authority
    isCorsCompliant actualOrigin childOrigin corsHeaders =
      case corsHeaders of
        [ expectedOrigin ]
          | expectedOrigin == "*" -> true -- allow any origin
          | expectedOrigin == actualOrigin -> true -- whitelisted origin
        _ | actualOrigin == childOrigin -> true -- origins match
          | otherwise -> false
    corsCompliant { headers, result } = result <$ do
      parent >>= case importType, _ of
        -- When child and parent are both remote imports …
        Remote (URL url), Just (Localized (Import { importType: Remote (URL url') }))
          -- check response headers with the origins of parent and child
          | expectedOrigins <- getHeader "Access-Control-Allow-Origin" headers
          , not (isCorsCompliant `on` toOrigin) url' url expectedOrigins ->
              throw $ Variant.inj (_S::S_ "Not CORS compliant")
                { expectedOrigins, actualOrigin: toOrigin url }
        _, _ -> pure unit

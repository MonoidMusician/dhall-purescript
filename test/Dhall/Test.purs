module Dhall.Test where

import Prelude

import Control.Comonad (extract)
import Control.Monad.Writer (WriterT)
import Data.Argonaut.Core (Json)
import Data.ArrayBuffer.Types (ArrayBuffer)
import Data.Either (Either(..))
import Data.Functor.Compose (Compose(..))
import Data.Functor.Product (Product, product)
import Data.Lazy (Lazy, defer)
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Traversable (class Traversable, traverse)
import Data.Tuple (Tuple(..), fst)
import Dhall.Core (Expr, Import, unordered)
import Dhall.Core as Dhall.Core
import Dhall.Core.CBOR (encode)
import Dhall.Imports.Hash as Hash
import Dhall.Imports.Resolve as Resolve
import Dhall.Imports.Retrieve as Retrieve
import Dhall.Lib.CBOR as CBOR
import Dhall.Map (class MapLike, InsOrdMap)
import Dhall.Map as IOSM
import Dhall.Parser as Parser
import Dhall.TypeCheck as TC
import Effect (Effect)
import Effect.Aff (Aff, runAff_)
import Effect.Class.Console (log, logShow)
import Effect.Exception (message)
import Validation.These as V

testAff :: forall a. Show a => Aff a -> Effect Unit
testAff = runAff_ case _ of
  Left err -> log (message err)
  Right a -> logShow a
parse :: String -> Maybe (Expr (InsOrdMap String) Import)
parse = Parser.parse
noImports :: forall f a. Traversable f => f a -> Maybe (f Void)
noImports = traverse (const Nothing)
resolve' :: Resolve.ImportExpr -> Aff (Resolve.Feedback () () Resolve.ResolvedExpr)
resolve' = resolve''
  { stack: mempty
  , retriever: Retrieve.nodeRetrieve
  , cacher: Retrieve.nodeCache
  }
resolve'' :: Resolve.R -> Resolve.ImportExpr -> Aff (Resolve.Feedback () () Resolve.ResolvedExpr)
resolve'' resolver e = Resolve.runM resolver { cache: IOSM.empty, toBeCached: mempty } (Resolve.resolveImportsHere e) <#> \(Tuple fb _) -> fb
resolve :: Expr (InsOrdMap String) Import -> Aff (Maybe (Expr (InsOrdMap String) Void))
resolve e = resolve' e <#> \fb -> V.hushW' fb
tc :: forall t14. MapLike String t14 => Expr t14 Void -> Maybe (Expr t14 Void)
tc = tc' >>> V.hush'
tc' :: forall t14. MapLike String t14 => Expr t14 Void -> TC.ResultE () t14 Void (Expr t14 Void)
tc' = TC.typeOf
normalize :: forall m a. MapLike String m => Eq a => Expr m a -> Expr m a
normalize = Dhall.Core.normalize

feedback :: forall f e a. Applicative f =>
  V.Erroring e a -> (e -> f Unit) -> (a -> f Unit) -> f Unit
feedback (V.Success a) _ g = g a
feedback (V.Error es ma) f g = void $ traverse f es *> traverse g ma

feedback' :: forall w f e a. Applicative f =>
  WriterT w (V.Erroring e) a -> (e -> f Unit) -> (a -> f Unit) -> f Unit
feedback' w f g = feedback (fst <$> unwrap w) f g

type LzMb = Compose Lazy Maybe
type Actions =
  { text :: String
  , parse :: LzMb
    { parsed :: Resolve.ImportExpr
    , unsafeNormalized :: Lazy Resolve.ImportExpr
    , encoded :: Lazy
      { json :: Json
      , cbor :: ArrayBuffer
      }
    , imports :: Product LzMb (Compose Aff (Resolve.Feedback () ()))
      { resolved :: Resolve.ResolvedExpr
      , encoded :: Lazy
        { json :: Json
        , cbor :: ArrayBuffer
        }
      , unsafeNormalized :: Lazy Resolve.ResolvedExpr
      , typechecked :: Compose Lazy (TC.ResultE () IOSM.InsOrdStrMap Void)
        { inferredType :: Resolve.ResolvedExpr
        , normalizedType :: Lazy Resolve.ResolvedExpr
        , safeNormalized :: Lazy Resolve.ResolvedExpr
        , encoded :: Lazy
          { json :: Json
          , cbor :: ArrayBuffer
          , hash :: String
          }
        }
      }
    }
  }

mkActions :: String -> Actions
mkActions = mkActions'
  { stack: mempty
  , retriever: Retrieve.nodeRetrieve
  , cacher: Retrieve.nodeCache
  }

mkActions' :: Resolve.R -> String -> Actions
mkActions' resolver text =
  { text
  , parse: Compose $ defer \_ -> parse text <#> \parsed ->
      { parsed
      , unsafeNormalized: defer \_ -> normalize parsed
      , encoded: defer \_ ->
          let
            json = encode $ unordered parsed
            cbor = CBOR.encode json
          in { json, cbor }
      , imports:
          product
            (Compose $ defer \_ -> traverse (const Nothing) parsed)
            (Compose $ resolve'' resolver parsed)
          <#> \resolved ->
          { resolved
          , unsafeNormalized: defer \_ -> normalize resolved
          , encoded: defer \_ ->
              let
                json = encode $ unordered parsed
                cbor = CBOR.encode json
              in { json, cbor }
          , typechecked: Compose $ defer \_ ->
              tc' resolved <#> \inferredType ->
                { inferredType
                , normalizedType: defer \_ -> normalize inferredType
                , safeNormalized: defer \_ -> normalize resolved
                , encoded: defer \_ ->
                    let
                      norm = Hash.neutralize (absurd <$> resolved)
                      hash = Hash.hash norm
                      json = encode norm
                      cbor = CBOR.encode json
                    in { json, cbor, hash }
                }
          }
      }
  }

execActions :: String -> Effect Unit
execActions text = case extract $ unwrap $ _.parse $ mkActions text of
  Nothing -> log "Parse error"
  Just { parsed, imports } ->
    logShow parsed *>
    flip runAff_ (unwrap $ extract $ unwrap imports)
    case _ of
      Left err -> log (message err)
      Right r ->
        feedback' r (\(TC.TypeCheckError { tag }) -> logShow tag)
          \{ resolved, typechecked } ->
            logShow resolved *>
            feedback (extract $ unwrap $ typechecked) (\(TC.TypeCheckError { tag }) -> logShow tag)
              \{ inferredType, safeNormalized } -> logShow
                { norm: extract safeNormalized
                , type: inferredType
                }

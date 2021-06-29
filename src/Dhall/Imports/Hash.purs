module Dhall.Imports.Hash where

import Prelude

import Data.ArrayBuffer.Types (ArrayBuffer)
import Dhall.Core (Expr, Import, alphaNormalize, conv, normalize, unordered)
import Dhall.Core.CBOR (encode)
import Dhall.Lib.CBOR as CBOR
import Dhall.Map (class MapLike)

-- Sort, normalize, alpha-normalize an expr for caching purposes.
neutralize :: forall m a. MapLike String m => Eq a => Expr m a -> Expr m a
neutralize = unordered >>> normalize >>> alphaNormalize >>> conv

foreign import sha256 :: ArrayBuffer -> String

hash :: forall m. MapLike String m => Expr m Import -> String
hash = encode >>> CBOR.encode >>> sha256

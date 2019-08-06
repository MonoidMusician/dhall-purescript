module Dhall.Core.Imports.Hash where

import Prelude

import Crypto.SJCL.Codec.ArrayBuffer (toBits)
import Crypto.SJCL.Codec.Hex as Hex
import Crypto.SJCL.Hash (sha256)
import Crypto.SJCL.Hash as SJCL
import Dhall.Core (Expr, Import, alphaNormalize, conv, normalize, unordered)
import Dhall.Core.CBOR (encode)
import Dhall.Lib.CBOR as CBOR
import Dhall.Map (class MapLike)

-- Sort, normalize, alpha-normalize an expr for caching purposes.
neutralize :: forall m a. MapLike String m => Eq a => Expr m a -> Expr m a
neutralize = unordered >>> normalize >>> alphaNormalize >>> conv

hash :: forall m. MapLike String m => Expr m Import -> String
hash = encode >>> CBOR.encode >>> toBits >>> SJCL.hash sha256 >>> Hex.fromBits

module Dhall.Lib.CBOR where

import Data.Argonaut.Core (Json)
import Data.ArrayBuffer.Types (ArrayBuffer)

foreign import encode :: Json -> ArrayBuffer
foreign import decode :: ArrayBuffer -> Json

module Dhall.Lib.CBOR where

import Data.Argonaut.Core (Json)
import Data.ArrayBuffer.Types (ArrayBuffer)

foreign import encode :: Json -> ArrayBuffer
foreign import decode :: ArrayBuffer -> Json

foreign import data Decimal :: Type
foreign import mkDecimal :: { exponent :: Int, mantissa :: Int } -> Decimal
foreign import unDecimal :: Decimal -> { exponent :: Int, mantissa :: Int }

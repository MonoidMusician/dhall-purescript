module Dhall.Lib.Numbers where

import Prelude
import Data.BigInt as BigInt
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.String as String
import Unsafe.Coerce (unsafeCoerce)

-- Number with actual equality
newtype Double = Double Number
derive instance newtypeDouble :: Newtype Double _
derive newtype instance showDouble :: Show Double
instance eqDouble :: Eq Double where
  eq (Double a) (Double b) = (a == b && recip a == recip b) || (a /= a && b /= b)
instance ordDouble :: Ord Double where
  compare a b | a == b = EQ
  compare (Double a) (Double b) = compare a b <> compare (recip a) (recip b)

-- Integer inherited from BigInt
newtype Integer = Integer BigInt.BigInt
derive instance newtypeInteger :: Newtype Integer _
derive newtype instance eqInteger :: Eq Integer
derive newtype instance ordInteger :: Ord Integer
derive newtype instance semiringInteger :: Semiring Integer
derive newtype instance ringInteger :: Ring Integer
instance showInteger :: Show Integer where
  show (Integer i) | i < zero = BigInt.toString i
  show (Integer i) = "+" <> BigInt.toString i

intToInteger :: Int -> Integer
intToInteger i = Integer (BigInt.fromInt i)

integerToInt :: Integer -> Int
integerToInt = unsafeCoerce integerToNumber

integerToInt' :: Integer -> Maybe Int
integerToInt' i0 =
  let i = integerToInt i0
      i2 = intToInteger i
  in if i0 == i2 then Just i else Nothing

integerToNumber :: Integer -> Number
integerToNumber (Integer i) = BigInt.toNumber i

integerFromString :: String -> Maybe Integer
integerFromString s =
  case String.stripPrefix (String.Pattern "-") s, String.stripPrefix (String.Pattern "+") s of
    Just s', _ -> negate <$> integerFromString s'
    _, Just s' -> integerFromString s'
    _, _ -> case String.stripPrefix (String.Pattern "0x") s of
      Just s' -> Integer <$> BigInt.fromBase 16 s'
      Nothing -> Integer <$> BigInt.fromString s

even :: Integer -> Boolean
even (Integer i) = BigInt.even i

newtype Natural = Natural BigInt.BigInt
derive instance newtypeNatural :: Newtype Natural _
derive newtype instance eqNatural :: Eq Natural
derive newtype instance ordNatural :: Ord Natural
derive newtype instance semiringNatural :: Semiring Natural
instance showNatural :: Show Natural where
  show (Natural i) = BigInt.toString i

naturalToInteger :: Natural -> Integer
naturalToInteger (Natural i) = Integer i

naturalFromInteger :: Integer -> Natural
naturalFromInteger (Integer i) | i >= zero = Natural i
naturalFromInteger _ = zero

naturalFromInt :: Int -> Natural
naturalFromInt = naturalFromInteger <<< Integer <<< BigInt.fromInt

monus :: Natural -> Natural -> Natural
monus (Natural a) (Natural b) = naturalFromInteger (Integer (a - b))

infixl 6 monus as +-

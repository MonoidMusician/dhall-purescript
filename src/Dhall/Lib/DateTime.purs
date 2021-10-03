module Dhall.Lib.DateTime ( module Dhall.Lib.DateTime, module Exports ) where

import Prelude

import Data.DateTime (Date) as Exports
import Data.DateTime (Hour, Millisecond, Minute, Second)
import Data.Enum (class BoundedEnum, class Enum, Cardinality(..), fromEnum, toEnum)
import Data.Maybe (Maybe(..))

newtype Nanosecond = Nanosecond Int

derive newtype instance eqNanosecond :: Eq Nanosecond
derive newtype instance ordNanosecond :: Ord Nanosecond

instance boundedNanosecond :: Bounded Nanosecond where
  bottom = Nanosecond 0
  top = Nanosecond 999999

instance enumNanosecond :: Enum Nanosecond where
  succ = toEnum <<< (_ + 1) <<< fromEnum
  pred = toEnum <<< (_ - 1) <<< fromEnum

instance boundedEnumNanosecond :: BoundedEnum Nanosecond where
  cardinality = Cardinality 1000000
  toEnum n
    | n >= 0 && n <= 999999 = Just (Nanosecond n)
    | otherwise = Nothing
  fromEnum (Nanosecond n) = n

instance showNanosecond :: Show Nanosecond where
  show (Nanosecond m) = "(Nanosecond " <> show m <> ")"

data Time = Time Hour Minute Second Millisecond Nanosecond

derive instance eqTime :: Eq Time
derive instance ordTime :: Ord Time

instance boundedTime :: Bounded Time where
  bottom = Time bottom bottom bottom bottom bottom
  top = Time top top top top top

instance showTime :: Show Time where
  show (Time h m s ms ns) = "(Time " <> show h <> " " <> show m <> " " <> show s <> " " <> show ms <> " " <> show ns <> ")"


data TimeZone = TimeZone Boolean Hour Minute

derive instance eqTimeZone :: Eq TimeZone
derive instance ordTimeZone :: Ord TimeZone

instance boundedTimeZone :: Bounded TimeZone where
  bottom = TimeZone false top top
  top = TimeZone true top top

instance showTimeZone :: Show TimeZone where
  show (TimeZone b h m) = "(TimeZone " <> show b <> " " <> show h <> " " <> show m <> ")"

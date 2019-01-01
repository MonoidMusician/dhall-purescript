module Dhall.Lib.DualAp where

import Prelude

import Data.Newtype (class Newtype)

newtype DualAp f a = DualAp (f a)
derive instance newtypeDualAp :: Newtype (DualAp f a) _
derive newtype instance functorDualAp :: Functor f => Functor (DualAp f)
instance applyDualAp :: Apply f => Apply (DualAp f) where
  apply (DualAp fab) (DualAp fa) = DualAp $ ((#) <$> fa) <*> fab
instance applicativeDualAp :: Applicative f => Applicative (DualAp f) where
  pure = DualAp <<< pure

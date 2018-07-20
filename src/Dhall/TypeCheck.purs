module Dhall.TypeCheck where

import Prelude
import Data.Either (Either(..))
import Dhall.Core.AST (Const(..))

axiom :: Const -> Either Unit Const
axiom Type = pure Kind
axiom Kind = Left unit

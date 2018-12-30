module Dhall.Core.AST.Operations.Location where

import Data.Lazy (Lazy)
import Dhall.Core.AST (Expr, ExprRowVFI, Var)

-- An expression for the user to look at when an error occurs, giving
-- specific context for what went wrong.
data Location a
  -- Atomic: The original tree being typechecked
  = MainExpression
  -- Derived: Pointer to a location within the prior location
  | LocationWithin (Lazy ExprRowVFI) (Location a)
  -- Derived: Point to the type of another location
  | TypeOfLocation (Location a)
  -- Derived: Point to the same location but normalized
  | NormalizeLocation (Location a)
  -- Atomic: A new expression, whose origin is shrouded in mystery ...
  | Place a
  -- Derived: The same expression, but with available `let`-bound variables
  -- substituted in from the local context.
  -- TODO: select specific variables to be substituted (`Set Var`?)
  | Substituted (Location a)
  -- Derived: The same expression, but with something _slightly_ different about it
  | Shifted Int Var (Location a)
type ExprLocation m a = Location (Expr m a)

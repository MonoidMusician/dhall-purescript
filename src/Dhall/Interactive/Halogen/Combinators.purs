module Dhall.Interactive.Halogen.Combinators where

import Prelude

type Combinators t =
  { basic ::
    -- identity
    { empty :: t
    -- juxtapose
    , combine :: t -> t -> t
    -- space
    , space :: t
    -- render a string directly
    , direct :: String -> t
    -- render an identifier
    , identifer :: String -> t
    -- render a keyword
    , keyword :: String -> t
    -- render an infix operator, plus or times, etc., with space around it
    , infix :: String -> t
    -- render a separator, like a comma (just a space after)
    , separator :: String -> t
    -- render a binder introduction (lambda or pi), no space
    , binder :: String -> t
    -- for parens, braces, brackets, etc.
    , surround :: { before :: String, after :: String } -> t -> t
    }
  , formatting ::
    -- just a newline
    { newline :: t
    -- possibly equivalent to intercalating newlines and `combine`ing
    , lines :: Array t -> t
    -- indent a block
    , indent ::
      -- whether there should be a newline before and after
      { clear :: { before :: Boolean, after :: Boolean }
      -- how many columns to indent by
      , amount :: Int
      -- whether the indent should be judged relative to the current column
      -- (that is, before any clearing newline)
      , relative :: Boolean
      } -> t -> t
    }
  , interactive ::
    -- for long arrays, records, etc.
    -- potentially interactive
    { vlist :: Array t -> t
    -- for short arrays on one line, etc.
    -- potentially interactive
    , hlist ::
      { items :: Array t
      , separator :: t
      } -> t
    }
  }

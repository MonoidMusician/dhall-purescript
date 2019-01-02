module Dhall.Core.AST.Noted where

import Prelude

import Control.Comonad (extract)
import Control.Comonad.Cofree (Cofree)
import Control.Comonad.Env (EnvT(..), mapEnvT, runEnvT, withEnvT)
import Data.Bifunctor (class Bifunctor, lmap)
import Data.Eq (class Eq1)
import Data.FunctorWithIndex (class FunctorWithIndex, mapWithIndex)
import Data.List (List(..), (:))
import Data.Newtype (class Newtype, unwrap, wrap)
import Data.Tuple (Tuple(..))
import Dhall.Core.AST.Types (ExprRowVF)
import Dhall.Core.AST.Types as Types
import Matryoshka (class Corecursive, class Recursive, embed, project, transCata)

newtype Expr m s a = Expr (Cofree (ExprRowVF m a) s)
derive instance newtypeExpr :: Newtype (Expr m s a) _
derive newtype instance eqExpr :: (Eq1 m, Eq s, Eq a) => Eq (Expr m s a)
instance recursiveExpr :: Recursive (Expr m s a) (EnvT s (ExprRowVF m a)) where
  project = unwrap >>> project >>> map wrap
instance corecursiveExpr :: Corecursive (Expr m s a) (EnvT s (ExprRowVF m a)) where
  embed = wrap <<< embed <<< map unwrap

instance bifunctorExpr :: Functor m => Bifunctor (Expr m) where
  bimap f g = transCata $ withEnvT f <<< mapEnvT (lmap g)

denote :: forall m s a. Expr m s a -> Types.Expr m a
denote = transCata $ runEnvT >>> extract

innote :: forall m s a. s -> Types.Expr m a -> Expr m s a
innote s = transCata $ EnvT <<< Tuple s

notateIndex :: forall m s a. FunctorWithIndex String m => Expr m (Types.ExprI -> s) a -> Expr m s a
notateIndex = notateIndexFrom Nil

notateIndexFrom :: forall m s a. FunctorWithIndex String m => Types.ExprI -> Expr m (Types.ExprI -> s) a -> Expr m s a
notateIndexFrom = go where
  go ix e = embed $ e # project
    # withEnvT ((#) ix)
    # mapEnvT (mapWithIndex \i' -> go $ pure i' : ix)

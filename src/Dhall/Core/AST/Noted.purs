module Dhall.Core.AST.Noted where

import Prelude

import Control.Comonad (extract)
import Control.Comonad.Env (EnvT(..), mapEnvT, runEnvT, withEnvT)
import Data.Bifunctor (class Bifunctor, lmap)
import Data.Functor.Mu (Mu)
import Data.Newtype (class Newtype, unwrap, wrap)
import Data.Tuple (Tuple(..))
import Dhall.Core.AST.Types (ExprRowVF)
import Dhall.Core.AST.Types as Types
import Matryoshka (class Corecursive, class Recursive, embed, project, transCata)

newtype Expr m s a = Expr (Mu (EnvT s (ExprRowVF m a)))
derive instance newtypeExpr :: Newtype (Expr m s a) _
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

module Dhall.TypeCheck.Types where

import Prelude

import Control.Comonad.Cofree (Cofree)
import Control.Comonad.Env (EnvT)
import Control.Monad.Writer (WriterT)
import Data.Bifoldable (bifoldMap, bifoldl, bifoldr)
import Data.Bifunctor (bimap)
import Data.Bitraversable (bisequence, bitraverse)
import Data.Foldable (class Foldable, foldMap, foldl, foldr)
import Data.Functor.Compose (Compose)
import Data.Functor.Product (Product)
import Data.Lazy (Lazy)
import Data.List (List)
import Data.List.Types (NonEmptyList)
import Data.Maybe (Maybe)
import Data.Natural (Natural)
import Data.Newtype (class Newtype)
import Data.NonEmpty (NonEmpty)
import Data.Semigroup.Foldable (class Foldable1)
import Data.Set (Set)
import Data.These (These)
import Data.Traversable (class Traversable, sequence, traverse)
import Data.Tuple (Tuple)
import Data.Variant (Variant)
import Dhall.Context (Context)
import Dhall.Core.AST (Var, Const, SimpleExpr)
import Dhall.Core.AST as AST
import Dhall.Core.AST.Operations.Location (BasedExprDerivation)
import Dhall.Normalize as Dhall.Normalize
import Validation.These as V

import Dhall.TypeCheck.Tree (HalfTwoD, TwoD)

-- Locations --

-- Annotated syntax tree based on Expr, pretty standard ...
type Ann m a = Cofree (AST.ExprRowVF m a)
-- Expressions end up being associated with many locations, trust me on this ...
type L m a = NonEmptyList (BasedExprDerivation m a)
-- Expr with Location for each node
type Lxpr m a = Ann m a (L m a)
-- Pattern Functor for Lxpr
type LxprF m a = EnvT (L m a) (AST.ExprRowVF m a)


-- Contexts --

-- Context of which variables have been introduced with their
-- types and/or values:
-- - `This`: `Let` binding with only a value and no type annotation
-- - `Both`: `Let` binding with a value and its type annotation
-- - `That`: `Lam`/`Pi` binding
type BiContext a = Context (These a a)
-- Context that only records which variables have concrete values in scope.
type SubstContext a = Context (Maybe a)
-- Product (Compose Context (Join These)) f, but without the newtypes
-- (I love newtypes, but even that was a little excessive for me ...)
data WithBiCtx f a = WithBiCtx (BiContext a) (f a)
getBiCtx :: forall f a. WithBiCtx f a -> BiContext a
getBiCtx (WithBiCtx ctx _) = ctx
dropBiCtx :: forall f a. WithBiCtx f a -> f a
dropBiCtx (WithBiCtx _ fa) = fa
overBiCtx :: forall f g a. (f a -> g a) -> WithBiCtx f a -> WithBiCtx g a
overBiCtx fg (WithBiCtx ctx fa) = WithBiCtx ctx (fg fa)
instance functorWithBiCtx :: Functor f => Functor (WithBiCtx f) where
  map f (WithBiCtx ctx fa) = WithBiCtx (join bimap f <$> ctx) (f <$> fa)
instance foldableWithBiCtx :: Foldable f => Foldable (WithBiCtx f) where
  foldMap f (WithBiCtx ctx fa) = foldMap (join bifoldMap f) ctx <> foldMap f fa
  foldr f c (WithBiCtx ctx fa) = foldr (flip $ join bifoldr f) (foldr f c fa) ctx
  foldl f c (WithBiCtx ctx fa) = foldl f (foldl (join bifoldl f) c ctx) fa
instance traversableWithBiCtx :: Traversable f => Traversable (WithBiCtx f) where
  traverse f (WithBiCtx ctx fa) = WithBiCtx <$> traverse (join bitraverse f) ctx <*> traverse f fa
  sequence (WithBiCtx ctx fa) = WithBiCtx <$> traverse bisequence ctx <*> sequence fa


-- Errors --

-- A single error
newtype TypeCheckError r a = TypeCheckError
  -- The main location where the typechecking error occurred
  { location :: a
  -- The tag for the specific error, mostly for machine purposes
  , tag :: Variant r
  }
derive instance functorTypeCheckError :: Functor (TypeCheckError r)
derive newtype instance showTypeCheckError :: (Show a, Show (Variant r)) => Show (TypeCheckError r a)

-- Writer-Error "monad" (not quite a monad, but has bind+applicative)
type WR w e = WriterT (Array (Variant w)) (V.Erroring e)
-- Writer-Error "monad" with type-checking errors specifically
type Feedback w r m a = WR w (TypeCheckError r (L m a))
-- Just the error "monad"
type Result r m a = V.Erroring (TypeCheckError r (L m a))

-- A record of conflict, when a list is supposed to agree but there are two
-- or more distinct elements or groupings.
newtype Inconsistency a = Inconsistency (NonEmpty (NonEmpty List) a)
derive instance newtypeInconsistency :: Newtype (Inconsistency a) _
derive newtype instance showInconsistency :: Show a => Show (Inconsistency a)
derive newtype instance functorInconsistency :: Functor Inconsistency
derive newtype instance foldableInconsistency :: Foldable Inconsistency
derive newtype instance foldable1Inconsistency :: Foldable1 Inconsistency
derive newtype instance traversableInconsistency :: Traversable Inconsistency
-- derive newtype instance traversable1Inconsistency :: Traversable1 Inconsistency

-- An open row of errors encountered during typechecking.
type Errors r =
  ( "Not a function" :: Unit
  , "Type mismatch" :: Unit
  , "Invalid predicate" :: Unit
  , "If branch mismatch" :: Unit
  , "If branch must be term" :: Boolean
  , "Invalid list type" :: Maybe Const
  , "Missing list type" :: Unit
  , "Invalid list element" :: Int
  , "Mismatched list elements" :: Int
  , "Cannot append non-list" :: Boolean
  , "Cannot interpolate" :: Natural
  , "List append mismatch" :: Unit
  , "List annotation must be list type" :: Unit
  , "Invalid `Some`" :: Maybe Const
  , "Duplicate record fields" :: NonEmptyList String
  , "Invalid field type" :: String
  , "Duplicate union alternatives" :: NonEmptyList String
  , "Invalid alternative type" :: String
  , "Inconsistent alternative types" :: Inconsistency (NonEmptyList String)
  , "Must combine a record" :: Tuple (List String) Boolean
  , "Must merge a record" :: Unit
  , "Must merge a union" :: Unit
  , "Missing merge type" :: Unit
  , "Missing handler" :: Set Unit
  , "Unused handlers" :: Set Unit
  , "Handler not a function" :: String
  , "Dependent handler function" :: String
  , "Handler input type mismatch" :: String
  , "Handler output type mismatch" :: Tuple (Maybe { key :: String, fn :: Boolean }) String
  , "Handler type mismatch" :: Tuple (Maybe { key :: String, fn :: Boolean }) String
  , "Cannot project" :: Unit
  , "Cannot project by expression" :: Unit
  , "Projection type mismatch" :: String
  , "Missing field" :: String
  , "Cannot access" :: Unit
  , "toMap takes a record" :: Unit
  , "Invalid toMap type annotation" :: Unit
  , "Invalid toMap type" :: Maybe Const
  , "Missing toMap type" :: Unit
  , "Inconsistent toMap types" :: Inconsistency (NonEmptyList (Maybe String))
  , "Wrong header type" :: Unit
  , "Invalid input type" :: Unit
  , "Invalid output type" :: Unit
  , "Unbound variable" :: Var
  , "Annotation mismatch" :: Unit
  , "Not an equivalence" :: Unit
  , "Assertion failed" :: Unit
  , "Incomparable expression" :: Boolean
  , "Equivalent type mismatch" :: Unit
  , "`Sort` has no type" :: Unit
  , "Unexpected type" :: Tuple Boolean SimpleExpr
  | r
  )
type ResultE r m a = Result (Errors r) m a
type FeedbackE w r m a = Feedback w (Errors r) m a
type OxprE w r m a = Oxpr w (Errors r) m a
type OsprE w r m a = Ospr w (Errors r) m a
type TypeCheckErrorE r a = TypeCheckError (Errors r) a

-- Operations --

-- Operations that can be performed on AST nodes:
--   Left left (Lazy): alphaNormalize
--   Left right left (Bicontext): current context
--   Left right right (Lazy W): substitution+normalization (idempotent, but this isn't optimized ...)
--   Right (Lazy Feedback): typechecking
-- TODO: extensibility? connect to GenericExprAlgebra?
type Operations w r m a = Product (Product Lazy (WithBiCtx (Compose Lazy Dhall.Normalize.W))) (Compose Lazy (Feedback w r m a))
-- Expr with Location, along the dual axes of Operations and the AST
type Oxpr w r m a = TwoD (Operations w r m a) (LxprF m a)
-- Oxpr where nodes may be shared/elaborated or plain branches
type Ospr w r m a = HalfTwoD (Operations w r m a) (LxprF m a)

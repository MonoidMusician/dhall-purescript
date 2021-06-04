module Dhall.API.Conversions where

import Prelude

import Control.Alt ((<|>))
import Data.Array as Array
import Data.Const as ConstF
import Data.Functor.Contravariant (class Contravariant)
import Data.Functor.Product (Product(..), product)
import Data.Identity (Identity(..))
import Data.Lens as Lens
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Maybe (Maybe(..), fromJust)
import Data.Maybe as Maybe
import Data.Newtype (class Newtype, over, unwrap)
import Data.Symbol (class IsSymbol, reflectSymbol)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Data.Unfoldable (class Unfoldable)
import Data.Variant (Variant)
import Data.Variant as Variant
import Dhall.Context as Dhall.Context
import Dhall.Core.AST (Expr, Pair(..), S_, _S)
import Dhall.Core.AST as AST
import Dhall.Lib.Numbers (Double(..), Natural, Integer)
import Dhall.Lib.Numbers as Num
import Dhall.Map as Dhall.Map
import Dhall.Normalize (GNormalizerF(..), Normalizer)
import Dhall.Normalize as Dhall.Normalize
import Dhall.Normalize.Apps (apps, noapplit, (~))
import Prim.Row as Row
import Prim.RowList (Nil, Cons, class RowToList)
import Record as Record
import Type.Proxy (Proxy(..))

type StandardExpr = Expr Dhall.Map.InsOrdStrMap Void

newtype Type a = Type
  { extract  :: StandardExpr -> Maybe a
  -- ^ Extracts Haskell value from the Dhall expression
  , expected :: StandardExpr
  -- ^ Dhall type of the Haskell value
  }
derive instance functorType :: Functor Type
derive instance newtypeType :: Newtype (Type a) _

type TypeT f = forall a. Type a -> Type (f a)

auto :: forall a. Interpret a => Type a
auto = autoWith defaultInterpretOptions

newtype InputType a = InputType
  { embed    :: a -> StandardExpr
  -- ^ Embeds a Haskell value as a Dhall expression
  , declared :: StandardExpr
  -- ^ Dhall type of the Haskell value
  }
derive instance newtypeInputType :: Newtype (InputType a) _

instance contravariantInputType :: Contravariant InputType where
  cmap f (InputType t) = InputType
    { embed: t.embed <<< f
    , declared: t.declared
    }

inject :: forall a. Inject a => InputType a
inject = injectWith defaultInterpretOptions

type InterpretOptions =
  { fieldModifier       :: String -> String
  -- ^ Function used to transform Haskell field names into their corresponding
  --   Dhall field names
  , constructorModifier :: String -> String
  -- ^ Function used to transform Haskell constructor names into their
  --   corresponding Dhall alternative names
  }

defaultInterpretOptions :: InterpretOptions
defaultInterpretOptions =
  { fieldModifier:       identity
  , constructorModifier: identity
  }

class Interpret a where
  autoWith :: InterpretOptions -> Type a

class Inject a where
  injectWith :: InterpretOptions -> InputType a

instance interpretBoolean :: Interpret Boolean where autoWith _ = boolean
boolean :: Type Boolean
boolean = Type
  { expected: AST.mkBool
  , extract: Lens.preview (AST._E AST._BoolLit <<< _Newtype)
  }
instance injectBoolean :: Inject Boolean where
  injectWith _ = InputType
    { declared: AST.mkBool
    , embed: AST.mkBoolLit
    }

instance interpretNatural :: Interpret Natural where autoWith _ = natural
natural :: Type Natural
natural = Type
  { expected: AST.mkNatural
  , extract: Lens.preview (AST._E AST._NaturalLit <<< _Newtype)
  }
instance injectNatural :: Inject Natural where
  injectWith _ = InputType
    { declared: AST.mkNatural
    , embed: AST.mkNaturalLit
    }

instance interpretInt :: Interpret Int where autoWith _ = int
int :: Type Int
int = Type
  { expected: AST.mkInteger
  , extract: Lens.preview (AST._E AST._IntegerLit <<< _Newtype) >>> map Num.integerToInt
  }
instance injectInt :: Inject Int where
  injectWith _ = InputType
    { declared: AST.mkInteger
    , embed: AST.mkIntegerLit <<< Num.intToInteger
    }

instance interpretInteger :: Interpret Integer where autoWith _ = integer
integer :: Type Integer
integer = Type
  { expected: AST.mkInteger
  , extract: Lens.preview (AST._E AST._IntegerLit <<< _Newtype)
  }
instance injectInteger :: Inject Integer where
  injectWith _ = InputType
    { declared: AST.mkInteger
    , embed: AST.mkIntegerLit
    }

instance interpretNumber :: Interpret Number where autoWith _ = number
number :: Type Number
number = Type
  { expected: AST.mkDouble
  , extract: Lens.preview (AST._E AST._DoubleLit <<< _Newtype <<< _Newtype)
  }
instance injectNumber :: Inject Number where
  injectWith _ = InputType
    { declared: AST.mkDouble
    , embed: AST.mkDoubleLit <<< Double
    }

instance interpretString :: Interpret String where autoWith _ = string
string :: Type String
string = Type
  { expected: AST.mkText
  , extract: Lens.preview (AST._E (AST._TextLit_single <<< Lens.iso ConstF.Const unwrap) <<< _Newtype)
  }
instance injectString :: Inject String where
  injectWith _ = InputType
    { declared: AST.mkText
    , embed: AST.mkTextLit'
    }

instance interpretMaybe :: Interpret a => Interpret (Maybe a) where
  autoWith = maybe <<< autoWith
maybe :: TypeT Maybe
maybe (Type a) = Type
  { expected: AST.mkApp AST.mkOptional a.expected
  , extract: \e -> extractSome e <|> extractNone e
  } where
    extractSome e = Lens.preview (AST._E (AST._ExprFPrism (_S::S_ "Some"))) e >>=
      \(Identity some) ->
        Just <$> a.extract some
    extractNone e = Lens.preview (AST._E (AST._ExprFPrism (_S::S_ "App"))) e >>=
      \(Pair none _) ->
        Nothing <$ Lens.preview (AST._E (AST._ExprFPrism (_S::S_ "None"))) none
instance injectMaybe :: Inject a => Inject (Maybe a) where
  injectWith opts = InputType
    { declared: AST.mkApp AST.mkOptional a.declared
    , embed: Maybe.maybe (AST.mkApp AST.mkNone a.declared) (AST.mkSome <<< a.embed)
    } where (InputType a :: InputType a) = injectWith opts

instance interpretArray :: Interpret a => Interpret (Array a) where
  autoWith = array <<< autoWith
array :: TypeT Array
array (Type a) = Type
  { expected: AST.mkApp AST.mkList a.expected
  , extract: \e -> Lens.preview (AST._E (AST._ExprFPrism (_S::S_ "ListLit"))) e >>=
    \(Product (Tuple _ es)) -> traverse a.extract es
  }
instance injectArray :: Inject a => Inject (Array a) where
  injectWith opts = InputType
    { declared: AST.mkApp AST.mkList a.declared
    , embed: AST.mkListLit (Just a.declared) <<< map a.embed
    } where (InputType a :: InputType a) = injectWith opts

unfoldable :: forall f. Unfoldable f => TypeT f
unfoldable = array >>> map Array.toUnfoldable

instance interpretVariant ::
  (RowToList r rl, InterpretRL rl r) => Interpret (Variant r) where
    autoWith = variant
variant :: forall rl r. RowToList r rl => InterpretRL rl r =>
  InterpretOptions -> Type (Variant r)
variant opts = Type
  { expected: AST.mkUnion $ pure <$> expectedV rl opts
  , extract: \e ->
    Lens.preview (AST._E (AST._ExprFPrism (_S::S_ "App"))) e >>=
      \(Pair field val) ->
        Lens.preview (AST._E (AST._ExprFPrism (_S::S_ "Field"))) field >>=
          \(Tuple key _) ->
            extractV rl opts key val
  } where rl = Proxy :: Proxy rl

instance interpretRecord ::
  (RowToList r rl, InterpretRL rl r) => Interpret (Record r) where
    autoWith = record
record :: forall rl r. RowToList r rl => InterpretRL rl r =>
  InterpretOptions -> Type (Record r)
record opts = Type
  { expected: AST.mkRecord $ expectedR rl opts
  , extract: \e ->
    Lens.preview (AST._E (AST._ExprFPrism (_S::S_ "RecordLit"))) e >>=
      extractR rl opts
  } where rl = Proxy :: Proxy rl

class InterpretRL rl r | rl -> r where
  expectedR :: Proxy rl -> InterpretOptions ->
    Dhall.Map.InsOrdStrMap StandardExpr
  expectedV :: Proxy rl -> InterpretOptions ->
    Dhall.Map.InsOrdStrMap StandardExpr
  extractR :: Proxy rl -> InterpretOptions ->
    Dhall.Map.InsOrdStrMap StandardExpr ->
    Maybe (Record r)
  extractV :: Proxy rl -> InterpretOptions ->
    String -> StandardExpr ->
    Maybe (Variant r)

instance interpretNil :: InterpretRL Nil () where
  expectedR _ _ = Dhall.Map.empty
  extractR _ _ _ = Just {}
  expectedV _ _ = Dhall.Map.empty
  extractV _ _ _ _ = Nothing

instance interpretCons ::
  ( IsSymbol s
  , Row.Cons s t r' r
  , Row.Lacks s r'
  , Row.Union r' singleton r
  , Interpret t
  , InterpretRL rl' r'
  ) => InterpretRL (Cons s t rl') r where
  expectedR _ opts =
    Dhall.Map.insert (opts.fieldModifier field) t.expected
      (expectedR (Proxy :: Proxy rl') opts)
    where
      (Type t :: Type t) = autoWith opts
      field = reflectSymbol (_S::S_ s)
  extractR _ opts vs = Record.insert (_S::S_ s)
    <$> (Dhall.Map.get (opts.fieldModifier field) vs >>= t.extract)
    <*> extractR (Proxy :: Proxy rl') opts vs
    where
      (Type t :: Type t) = autoWith opts
      field = reflectSymbol (_S::S_ s)
  expectedV _ opts =
    Dhall.Map.insert (opts.constructorModifier field) t.expected
      (expectedV (Proxy :: Proxy rl') opts)
    where
      (Type t :: Type t) = autoWith opts
      field = reflectSymbol (_S::S_ s)
  extractV _ opts key v =
    if key == opts.constructorModifier field
      then t.extract v <#> Variant.inj (_S::S_ s)
      else extractV (Proxy :: Proxy rl') opts key v <#> Variant.expand
    where
      (Type t :: Type t) = autoWith opts
      field = reflectSymbol (_S::S_ s)

instance injectVariant ::
  (RowToList r rl, InjectRL rl r) => Inject (Variant r) where
    injectWith opts = InputType
      { declared: AST.mkUnion $ pure <$> declaredV rl opts
      , embed: embedV rl opts >>>
          \(Product (Tuple (Tuple key val) tys)) ->
            AST.mkApp (AST.mkField (AST.mkUnion $ pure <$> declaredV rl opts) key) val
      } where rl = Proxy :: Proxy rl

instance injectRecord ::
  (RowToList r rl, InjectRL rl r) => Inject (Record r) where
    injectWith opts = InputType
      { declared: AST.mkRecord $ declaredR rl opts
      , embed: AST.mkRecordLit <<< embedR rl opts
      } where rl = Proxy :: Proxy rl

class InjectRL rl r | rl -> r where
  declaredR :: Proxy rl -> InterpretOptions ->
    Dhall.Map.InsOrdStrMap StandardExpr
  declaredV :: Proxy rl -> InterpretOptions ->
    Dhall.Map.InsOrdStrMap StandardExpr
  embedR :: Proxy rl -> InterpretOptions -> Record r ->
    Dhall.Map.InsOrdStrMap StandardExpr
  embedV :: Proxy rl -> InterpretOptions -> Variant r ->
    Product (Tuple String) Dhall.Map.InsOrdStrMap StandardExpr

instance injectNil :: InjectRL Nil () where
  declaredR _ _ = Dhall.Map.empty
  embedR _ _ _ = Dhall.Map.empty
  declaredV _ _ = Dhall.Map.empty
  embedV _ _ = Variant.case_

instance injectCons ::
  ( IsSymbol s
  , Row.Cons s t r' r
  , Row.Lacks s r'
  , Row.Union r' singleton r
  , Inject t
  , InjectRL rl' r'
  ) => InjectRL (Cons s t rl') r where
  declaredR _ opts =
    Dhall.Map.insert (opts.fieldModifier field) t.declared
      (declaredR (Proxy :: Proxy rl') opts)
    where
      (InputType t :: InputType t) = injectWith opts
      field = reflectSymbol (_S::S_ s)
  embedR _ opts vs = Dhall.Map.insert (opts.fieldModifier field)
      do Record.get (_S::S_ s) vs # t.embed
      do Record.delete (_S::S_ s) vs # embedR (Proxy :: Proxy rl') opts
    where
      (InputType t :: InputType t) = injectWith opts
      field = reflectSymbol (_S::S_ s)
  declaredV _ opts =
    Dhall.Map.insert (opts.constructorModifier field) t.declared
      (declaredV (Proxy :: Proxy rl') opts)
    where
      (InputType t :: InputType t) = injectWith opts
      field = reflectSymbol (_S::S_ s)
  embedV _ opts =
    Variant.on (_S::S_ s)
      do \v -> product
            do Tuple (opts.constructorModifier field) (t.embed v)
            do declaredV (Proxy :: Proxy rl') opts
      do embedV (Proxy :: Proxy rl') opts >>>
          (map >>> over Product) (Dhall.Map.insert (opts.constructorModifier field) t.declared)
    where
      (InputType t :: InputType t) = injectWith opts
      field = reflectSymbol (_S::S_ s)

interpretFnWith :: forall a b. Partial =>
  InputType a -> Type b ->
  Normalizer Dhall.Map.InsOrdStrMap Void ->
  Type (a -> b)
interpretFnWith (InputType a :: InputType a) (Type b :: Type b) ctx = Type
  { expected: AST.mkArrow a.declared b.expected
  , extract: \e -> Just \i -> fromJust (b.extract (Dhall.Normalize.normalizeWith ctx (AST.mkApp e (a.embed i))))
  }

type InjectFn instances fnty =
  instances ->
    { ty :: StandardExpr
    , normalize :: String -> fnty -> Normalizer Dhall.Map.InsOrdStrMap Void
    }

injectFnArg :: forall input instances fnty.
  InjectFn instances fnty ->
  InjectFn (Tuple (Type input) instances) (input -> fnty)
injectFnArg mkRest (Tuple (Type input) instances) =
  let rest = mkRest instances in
  { ty: AST.mkArrow input.expected rest.ty
  , normalize: \name fn -> GNormalizer \_ -> case _ of
      rest' ~ arg
        | Just arg' <- input.extract (Lens.review apps arg) ->
          unwrap (rest.normalize name (fn arg')) unit rest'
      _ -> Nothing
  }

injectFn :: forall i o. InjectFn (Tuple (Type i) (InputType o)) (i -> o)
injectFn (Tuple (Type i :: Type i) (InputType o :: InputType o)) =
  { ty: AST.mkArrow i.expected o.declared
  , normalize: \name fn -> GNormalizer \_ -> case _ of
    namedfn ~ arg
      | Just (AST.V name' 0) <- noapplit AST._Var namedfn
      , name' == name
      , Just arg' <- i.extract (Lens.review apps arg) ->
        Just \_ -> o.embed (fn arg')
    _ -> Nothing
  }

injectToContext :: forall fnty.
  { ty :: StandardExpr
  , normalize :: String -> fnty -> Normalizer Dhall.Map.InsOrdStrMap Void
  } ->
  String ->
  { ctx :: Dhall.Context.Context StandardExpr
  , normalize :: fnty -> Normalizer Dhall.Map.InsOrdStrMap Void
  }
injectToContext { ty, normalize } name =
  { ctx: Dhall.Context.Context $ pure $ Tuple name ty
  , normalize: normalize name
  }

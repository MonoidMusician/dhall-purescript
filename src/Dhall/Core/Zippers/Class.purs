module Dhall.Core.Zippers where

import Prelude

import Control.Comonad (class Comonad, class Extend, extract)
import Control.Comonad.Env (EnvT)
import Data.Array as Array
import Data.Const (Const(..))
import Data.Either (Either(..))
import Data.Eq (class Eq1)
import Data.FoldableWithIndex (class FoldableWithIndex)
import Data.FoldableWithIndex as FoldableWithIndex
import Data.Functor.Compose (Compose(..))
import Data.Functor.Coproduct (Coproduct(..))
import Data.Functor.Coproduct as Coproduct
import Data.Functor.Product (Product(..))
import Data.Functor.Product as Product
import Data.Functor.Variant (FProxy, SProxy(..), VariantF)
import Data.Functor.Variant as VariantF
import Data.FunctorWithIndex (class FunctorWithIndex, mapWithIndex)
import Data.FunctorWithIndex as FunctorWithIndex
import Data.Identity (Identity(..))
import Data.Lazy (Lazy, defer)
import Data.Lens (Lens, Lens', Prism', elementsOf, firstOf, iso, lens, prism', re)
import Data.Lens.Indexed (itraversed, unIndex)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Maybe (Maybe(..), fromJust)
import Data.Map (Map)
import Data.Map as Map
import Data.Natural (Natural)
import Data.Newtype (class Newtype)
import Data.Ord (class Ord1)
import Data.Profunctor.Strong ((&&&))
import Data.Symbol (class IsSymbol)
import Data.Traversable (class Foldable, class Traversable)
import Data.Traversable as Traversable
import Data.TraversableWithIndex (class TraversableWithIndex)
import Data.TraversableWithIndex as TraversableWithIndex
import Data.Tuple (Tuple(..), uncurry)
import Data.Variant (Variant)
import Data.Variant as Variant
import Dhall.Core.AST.Types.Basics as Basics
import Partial.Unsafe (unsafePartial)
import Type.Row (RLProxy(..), Nil)
import Type.Row as Row

{-
FunctorWithIndex i f
let (m :: Type -> Type) (s a :: Type) be given,
let f = ExprRowVF m s a,
-- collect derivatives with VariantF
let DF f = VariantF (map (\t -> Diff1 t t' => t') f.row),
-- collect indices in a Variant
let i = Variant (map (\t -> FunctorWithIndex ti t => ti) f.row),

upZF   :: forall x. ZF f' x  ->       f  x
downZF :: forall x.    f  x  -> f (ZF f' x)

-- each derivative has an index it is associated with
ixF :: forall x. DF f x -> i
-- ZF consists of DF ...
_contextZF :: forall x. Lens' (ZF f x) (DF f x)
-- ... plus a focus
_focusZF :: forall x. Lens' (ZF f x) x
-- every zipper can be turned into an equivalent index and functor,
-- but not every index and functor form a valid zipper
_ix_wholeZF :: forall x. Prism' (EnvT i f x) (ZF f x)
_ix_wholeZF = prism'
  -- put the index and full structure into the EnvT
  (\zf -> EnvT (Tuple (ix (view _contextZF zf)) (upZF zf)))
  -- take the index and full structure and find the corresponding zipper from down
  \(EnvT (Tuple i f)) ->
    map _.value $ findWithIndex (pure <<< eq i) $ downZF f

Laws:
- upZF must undo downZF:
  \(f :: f x) ->
    all (eq f) (upZF <$> downZF f)
- zippers produced from down must match the indices they came from:
  \(f :: f x) ->
    and $ mapWithIndex (\i zf -> i == ix (view _contextZF zf)) $ downZF f
- zippers can be decomposed into their index and full functor (just a Prism law)
  \(zf :: ZF f x) ->
    preview _ix_wholeZF (review _ix_wholeZF zf) == Just zf

topE :: forall m s a. Expr m s a -> ZExpr m s a
upE :: forall m s a. ZExpr m s a -> Expr m s a
upwardsE :: forall m s a. ZExpr m s a -> Either (Expr m s a) (ZExpr m s a)
uptowardsTopE :: forall m s a. ZExpr m s a -> ZExpr m s a
downE :: forall m s a. ZExpr m s a -> ExprLayerF m s a (ZExpr m s a)
ixE :: forall m s a. ZExpr m s a -> IExpr m (s) (a)
_modifyAtE :: forall m s a. IExpr m (s) (a) -> Traversal' (Expr m s a) (Expr m s a)
_contextE :: forall m s a. Lens' (ZExpr m s a) (DExpr m s (a))
_focusE :: forall m s a. Lens' (ZExpr m s a) (Expr m s a)
_ix_zipperE :: forall m s a. Prism' (Tuple (IExpr m (s) (a)) (Expr m s a)) (ZExpr m s a)

-}

class ContainerI i f' | f' -> i where
  ixF :: forall x. f' x -> i
class (Eq1 f, Eq1 f', Ord i, TraversableWithIndex i f, Traversable f', ContainerI i f', Functor f', Functor f) <= Container i f f' | f -> i f', f' -> i where
  upZF   :: forall x. ZF f' x  ->      f  x
  downZF :: forall x.    f  x -> f (ZF f' x)

class FunctorWithIndexRL rl is fs | rl -> is fs where
  mapWithIndexRL :: forall a b. RLProxy rl ->
    (Variant is -> a -> b) -> VariantF fs a -> VariantF fs b

instance functorWithIndexRLNil :: FunctorWithIndexRL Nil () () where
  mapWithIndexRL _ _ = VariantF.case_

instance functorWithIndexRLCons ::
  ( IsSymbol s
  , FunctorWithIndex i f
  , Row.Cons s (FProxy f) fs' fs
  , Row.Cons s i is' is
  , Row.Union is' is_ is
  , Row.Union fs' fs_ fs
  , FunctorWithIndexRL rl' is' fs'
  ) => FunctorWithIndexRL (Row.Cons s (FProxy f) rl') is fs where
  mapWithIndexRL _ f = VariantF.on s
    (mapWithIndex (Variant.inj s >>> f) >>> VariantF.inj s)
    (mapWithIndexRL (RLProxy :: RLProxy rl') (f <<< Variant.expand) >>> VariantF.expand)
    where s = SProxy :: SProxy s

class ContainerIRL rl is f's | rl -> is f's where
  ixFRL :: forall x. RLProxy rl -> VariantF f's x -> Variant is

instance containerIRLNil :: ContainerIRL Nil () () where
  ixFRL _ = VariantF.case_

instance containerIRLCons ::
  ( IsSymbol s
  , ContainerI i f'
  , Row.Cons s (FProxy f') f's' f's
  , Row.Cons s i is' is
  , Row.Union is' is_ is
  , ContainerIRL rl' is' f's'
  ) => ContainerIRL (Row.Cons s (FProxy f') rl') is f's where
  ixFRL _ = VariantF.on s (ixF >>> Variant.inj s)
    (ixFRL (RLProxy :: RLProxy rl') >>> Variant.expand)
    where s = SProxy :: SProxy s

class ContainerRL rl (is :: # Type) fs f's | rl -> is fs f's where
  upZFRL :: forall x. RLProxy rl -> ZF (VariantF f's) x -> VariantF fs x
  downZFRL :: forall x. RLProxy rl -> VariantF fs x -> VariantF fs (ZF (VariantF f's) x)

instance containerRLNil :: ContainerRL Nil () () () where
  upZFRL _ (_ :<-: z) = VariantF.case_ (extract z)
  downZFRL _ = VariantF.case_

instance containerRLCons ::
  ( IsSymbol s
  , Functor f'
  , Container i f f'
  , Row.Cons s (FProxy f) fs' fs
  , Row.Cons s (FProxy f') f's' f's
  , Row.Cons s i is' is
  , Row.Union fs' fs_ fs
  , Row.Union f's' f's_ f's
  , ContainerRL rl' is' fs' f's'
  ) => ContainerRL (Row.Cons s (FProxy f) rl) is fs f's where
  upZFRL _ (a :<-: z) = VariantF.on s
    (\z' -> upZF (a :<-: pure z') # VariantF.inj s)
    (\z' -> upZFRL (RLProxy :: RLProxy rl') (a :<-: pure z') # VariantF.expand)
    (extract z)
    where s = SProxy :: SProxy s
  downZFRL _ = VariantF.on s
    (downZF >>> mapper (VariantF.inj s) (VariantF.inj s))
    (downZFRL (RLProxy :: RLProxy rl') >>> mapper VariantF.expand VariantF.expand)
    where s = SProxy :: SProxy s

-- Random utilities
mapper :: forall f g f' g' a. Functor f => (f ~> g) -> (f' a -> g' a) -> f (ZF f' a) -> g (ZF g' a)
mapper fg f'g' = (map <<< _contextZF' <<< map) f'g' >>> fg

deferAp :: forall a b. (a -> b) -> a -> Lazy b
deferAp f a = defer \_ -> f a

-- Datatypes and operations on zippers

-- A focus and with its (lazy) context
-- (`f` is most often `f'` that is the derivative of some container)
data ZF f x = ZF x (Lazy (f x))
-- The arrow points to the focus
infix 1 ZF as :<-:

-- This implements `duplicate` for the `ZF` comonad
aroundZF :: forall i f f' x. Container i f f' => ZF f x  -> ZF f (ZF f x)
aroundZF z@(_ :<-: cx) =
  z :<-: defer \_ ->
    downZF (extract cx) <#> upZF_f'
  where
    upZF_f' :: ZF f' x -> ZF f x
    upZF_f' z'@(x :<-: _) = x :<-: deferAp upZF z'

instance functorZF :: Functor f => Functor (ZF f) where
  map f (x :<-: f'x) = f x :<-: map f <$> f'x
instance extendZF :: Container i f f' => Extend (ZF f) where
  extend f = map f <<< aroundZF
instance comonadZF :: Container i f f' => Comonad (ZF f) where
  extract (x :<-: _) = x

ixZF :: forall i f x. ContainerI i f => ZF f x -> i
ixZF (_ :<-: z) = ixF (extract z)

-- Lookup a zipper by its index in the functor
previewIndexZF :: forall i f f' x. Container i f f' => i -> f x -> Maybe (ZF f' x)
previewIndexZF i = firstOf (unIndex $ elementsOf itraversed $ eq i) <<< downZF

unsafeGetIndexZF :: forall i f f' x. Container i f f' => Partial => i -> f x -> ZF f' x
unsafeGetIndexZF i f = fromJust $ previewIndexZF i f

_contextZF :: forall f g x. Lens (ZF f x) (ZF g x) (f x) (g x)
_contextZF = _contextZF' <<< iso extract pure

_contextZF' :: forall f g x. Lens (ZF f x) (ZF g x) (Lazy (f x)) (Lazy (g x))
_contextZF' = lens (\(_ :<-: fx) -> fx)
  \(x :<-: _) fx -> x :<-: fx

_focusZF :: forall f x. Lens' (ZF f x) x
_focusZF = lens (\(x :<-: _) -> x)
  \(_ :<-: fx) x -> x :<-: fx

_ix_wholeZF :: forall i f f' x. Container i f f' => Prism' (EnvT i f x) (ZF f' x)
_ix_wholeZF = _Newtype <<< prism' (ixZF &&& upZF) (uncurry previewIndexZF)

-- A zipper _of_ the type `f'`, _for_ the type `f` (with `Container i f f'`)
-- This allows instances that reference f, the "original" type
newtype ZF4 (f :: Type -> Type) f' x = ZF4 (ZF f' x)
derive instance newtypeZF4 :: Newtype (ZF4 f f' x) _

zf4 :: forall f f' x. FProxy f -> ZF f' x -> ZF4 f f' x
zf4 _ = ZF4

unZF4 :: forall f f' x. ZF4 f f' x -> ZF f' x
unZF4 (ZF4 z) = z

upZF4 :: forall i f f' x. Container i f f' => ZF4 f f' x -> f x
upZF4 = upZF <<< unZF4

downZF4 :: forall i f f' x. Container i f f' => f x -> f (ZF4 f f' x)
downZF4 = downZF >>> map ZF4

ixZF4 :: forall i f f' x. ContainerI i f' => ZF4 f f' x -> i
ixZF4 = ixZF <<< unZF4

previewIndexZF4 :: forall i f f' x. Container i f f' => i -> f x -> Maybe (ZF4 f f' x)
previewIndexZF4 i = map ZF4 <<< previewIndexZF i

unsafeGetIndexZF4 :: forall i f f' x. Container i f f' => Partial => i -> f x -> ZF4 f f' x
unsafeGetIndexZF4 i f = ZF4 $ unsafeGetIndexZF i f

derive newtype instance functorZF4 :: Functor f' => Functor (ZF4 f f')
derive newtype instance extendZF4 :: Container i f' f'' => Extend (ZF4 f f')
derive newtype instance comonadZF4 :: Container i f' f'' => Comonad (ZF4 f f')

instance foldableZF4 :: (Foldable f, Container i f f') => Foldable (ZF4 f f') where
  foldMap f = upZF4 >>> Traversable.foldMap f
  foldl f b = upZF4 >>> Traversable.foldl f b
  foldr f b = upZF4 >>> Traversable.foldr f b
-- `unsafeGetIndexZF4 (ixZF4 z)` is safe because `traverse` is preserves
-- structure, and the result of `upZF4` should contain the original zipper;
-- thus, a zipper at the index of the original should appear in the result
-- of `traverse`.
instance traversableZF4 :: (Traversable f, Functor f', Container i f f') => Traversable (ZF4 f f') where
  traverse f z = unsafePartial
    (upZF4 z # Traversable.traverse f # map (unsafeGetIndexZF4 (ixZF4 z)))
  sequence z = unsafePartial
    (upZF4 z # Traversable.sequence # map (unsafeGetIndexZF4 (ixZF4 z)))

instance functorWithIndexZF4 :: (FunctorWithIndex i f, Traversable f, Functor f', Container i f f') => FunctorWithIndex i (ZF4 f f') where
  mapWithIndex f z = unsafePartial
    (upZF4 z # FunctorWithIndex.mapWithIndex f # unsafeGetIndexZF4 (ixZF4 z))
instance foldableWithIndexZF4 :: (FoldableWithIndex i f, Container i f f') => FoldableWithIndex i (ZF4 f f') where
  foldMapWithIndex f = upZF4 >>> FoldableWithIndex.foldMapWithIndex f
  foldlWithIndex f b = upZF4 >>> FoldableWithIndex.foldlWithIndex f b
  foldrWithIndex f b = upZF4 >>> FoldableWithIndex.foldrWithIndex f b
instance traversableWithIndexZF4 :: (TraversableWithIndex i f, Functor f', Container i f f') => TraversableWithIndex i (ZF4 f f') where
  traverseWithIndex f z = unsafePartial
    (upZF4 z # TraversableWithIndex.traverseWithIndex f # map (unsafeGetIndexZF4 (ixZF4 z)))

_contextZF4 :: forall f f' g g' x. Lens (ZF4 f f' x) (ZF4 g g' x) (f' x) (g' x)
_contextZF4 = _Newtype <<< _contextZF

_contextZF4' :: forall f f' g g' x. Lens (ZF4 f f' x) (ZF4 g g' x) (Lazy (f' x)) (Lazy (g' x))
_contextZF4' = _Newtype <<< _contextZF'

_focusZF4 :: forall f f' x. Lens' (ZF4 f f' x) x
_focusZF4 = _Newtype <<< _focusZF

_ix_wholeZF4 :: forall i f f' x. Container i f f' => Prism' (EnvT i f x) (ZF4 f f' x)
_ix_wholeZF4 = _ix_wholeZF <<< re _Newtype

-- Container instances for common datatypes:
instance containerIConstVoid :: ContainerI Void (Const Void) where
  ixF (Const void) = void
else instance containerIConst :: ContainerI Unit (Const a) where
  ixF (Const _) = unit

instance containerIIdentity :: ContainerI Unit Identity where
  ixF (Identity _) = unit

type Const' = Const Void

{-
instance containerConst :: Eq a => Container Void (Const a) (Const Void) where
  upZF (_ :<-: void) = absurd $ unwrap $ extract void
  downZF (Const a) = Const a
-}

instance containerICoproduct :: (ContainerI i f', ContainerI j g') => ContainerI (Either i j) (Coproduct f' g') where
  ixF (Coproduct (Left cf)) = Left $ ixF cf
  ixF (Coproduct (Right cg)) = Right $ ixF cg

-- Sum rule: (f + g)' = f' + g'
instance containerCoproduct :: (Eq1 f, Eq1 g, Functor f', Functor g', Container i f f', Container j g g') =>
  Container (Either i j) (Coproduct f g) (Coproduct f' g') where
    downZF (Coproduct (Left f)) = downZF f # mapper Coproduct.left Coproduct.left
    downZF (Coproduct (Right g)) = downZF g # mapper Coproduct.right Coproduct.right
    upZF (a :<-: z) = case extract z of
      Coproduct (Left zf) -> Coproduct.left (upZF (a :<-: pure zf))
      Coproduct (Right zf) -> Coproduct.right (upZF (a :<-: pure zf))

-- Product rule: (f * g)' = (f' * g) + (g' * f)
newtype Product' f f' g g' a = Product' (Coproduct (Product f' g) (Product f g') a)
derive instance newtypeProduct' :: Newtype (Product' f f' g g' a) _
derive newtype instance eqProduct' :: (Eq1 f, Eq1 f', Eq1 g, Eq1 g', Eq a) => Eq (Product' f f' g g' a)
derive newtype instance ordProduct' :: (Ord1 f, Ord1 f', Ord1 g, Ord1 g', Ord a) => Ord (Product' f f' g g' a)
derive newtype instance eq1Product' :: (Eq1 f, Eq1 f', Eq1 g, Eq1 g') => Eq1 (Product' f f' g g')
derive newtype instance ord1Product' :: (Ord1 f, Ord1 f', Ord1 g, Ord1 g') => Ord1 (Product' f f' g g')
derive newtype instance functorProduct' :: (Functor f, Functor f', Functor g, Functor g') => Functor (Product' f f' g g')
derive newtype instance foldableProduct' :: (Foldable f, Foldable f', Foldable g, Foldable g') => Foldable (Product' f f' g g')
derive newtype instance traversableProduct' :: (Traversable f, Traversable f', Traversable g, Traversable g') => Traversable (Product' f f' g g')

instance containerIProduct :: (ContainerI i f', ContainerI j g') => ContainerI (Either i j) (Product' f f' g g') where
  ixF (Product' (Coproduct (Left (Product (Tuple cf _))))) = Left $ ixF cf
  ixF (Product' (Coproduct (Right (Product (Tuple _ cf))))) = Right $ ixF cf

instance containerProduct :: (Eq1 f, Eq1 g, Functor f', Functor g', Traversable f, Traversable g, Container i f f', Container j g g') =>
  Container (Either i j) (Product f g) (Product' f f' g g') where
    downZF (Product (Tuple f g)) = Product $ Tuple
      (downZF f # mapper identity \cf ->
        Product' (Coproduct (Left (Product (Tuple cf g)))))
      (downZF g # mapper identity \cg ->
        Product' (Coproduct (Right (Product (Tuple f cg)))))
    upZF (a :<-: z) = case extract z of
      Product' (Coproduct (Left (Product (Tuple cf g)))) ->
        Product.product (upZF (a :<-: pure cf)) g
      Product' (Coproduct (Right (Product (Tuple f cg)))) ->
        Product.product f (upZF (a :<-: pure cg))

-- Chain rule: (f ∘ g)' = (f' ∘ g) * g'
newtype Compose' f' g g' a = Compose' (Product (Compose f' g) g' a)
derive instance newtypeCompose' :: Newtype (Compose' f' g g' a) _
derive newtype instance eqCompose' :: (Eq1 f', Eq1 g, Eq1 g', Eq a) => Eq (Compose' f' g g' a)
derive newtype instance ordCompose' :: (Ord1 f', Ord1 g, Ord1 g', Ord a) => Ord (Compose' f' g g' a)
derive newtype instance eq1Compose' :: (Eq1 f', Eq1 g, Eq1 g') => Eq1 (Compose' f' g g')
derive newtype instance ord1Compose' :: (Ord1 f', Ord1 g, Ord1 g') => Ord1 (Compose' f' g g')
derive newtype instance functorCompose' :: (Functor f', Functor g, Functor g') => Functor (Compose' f' g g')
derive newtype instance foldableCompose' :: (Foldable f', Foldable g, Foldable g') => Foldable (Compose' f' g g')
derive newtype instance traversableCompose' :: (Traversable f', Traversable g, Traversable g') => Traversable (Compose' f' g g')

instance containerICompose :: (ContainerI i f', ContainerI j g') =>
  ContainerI (Tuple i j) (Compose' f' g g') where
    ixF (Compose' (Product (Tuple (Compose f'g) g'))) = Tuple (ixF f'g) (ixF g')

instance containerCompose :: (Eq1 f, Eq1 g, Functor f', Functor g', Traversable g, Container i f f', Container j g g') =>
  Container (Tuple i j) (Compose f g) (Compose' f' g g') where
    downZF (Compose fg) = Compose $ downZF fg <#> \(g :<-: f'g) ->
      downZF g # mapper identity \a ->
        Compose' (Product.product (Compose (extract f'g)) a)
    upZF (a :<-: z) = case extract z of
      Compose' (Product (Tuple (Compose f'g) g')) -> Compose $ upZF $
        upZF (a :<-: pure g') :<-: pure f'g

type Maybe' = Const Unit

instance containerMaybe :: Container Unit Maybe (Const Unit) where
  upZF (a :<-: z) = case extract z of
    Const (_ :: Unit) -> Just a
  downZF Nothing = Nothing
  downZF (Just a) = Just (a :<-: pure (Const unit))

{-
type Tuple' c = Const c

instance containerTuple :: (Eq c) => Container Unit (Tuple c) (Const c) where
  upZF (a :<-: z) = case extract z of
    Const c -> Tuple c a
  downZF (Tuple c a) = Tuple c (a :<-: pure (Const c))
-}

newtype Array' a = ArrayN (Product Array Array a)
derive instance newtypeArray' :: Newtype (Array' a) _
derive newtype instance eqArray' :: Eq a => Eq (Array' a)
derive newtype instance ordArray' :: Ord a => Ord (Array' a)
derive newtype instance eq1Array' :: Eq1 Array'
derive newtype instance ord1Array' :: Ord1 Array'
derive newtype instance functorArray' :: Functor Array'
derive newtype instance foldableArray' :: Foldable Array'
derive newtype instance traversableArray' :: Traversable Array'

arrayN :: forall a. Array a -> Array a -> Array' a
arrayN prev next = ArrayN (Product (Tuple prev next))

instance containerIArray :: ContainerI (Int) Array' where
  ixF (ArrayN (Product (Tuple prev _))) = Array.length prev

instance containerArray :: Container (Int) Array Array' where
  upZF (a :<-: z) = case extract z of
    ArrayN (Product (Tuple prev next)) -> prev <> [a] <> next
  downZF as = let l = Array.length as in as # mapWithIndex \i a ->
    a :<-: defer \_ -> arrayN (Array.slice 0 i as) (Array.slice (i+1) l as)

newtype Map' k a = Map' (Product (Const k) (Map k) a)
derive instance newtypeMap' :: Newtype (Map' k a) _
derive newtype instance eqMap' :: (Eq k, Eq a) => Eq (Map' k a)
derive newtype instance ordMap' :: (Ord k, Ord a) => Ord (Map' k a)
derive newtype instance eq1Map' :: Eq k => Eq1 (Map' k)
derive newtype instance ord1Map' :: Ord k => Ord1 (Map' k)
derive newtype instance functorMap' :: Functor (Map' k)
derive newtype instance foldableMap' :: Foldable (Map' k)
derive newtype instance traversableMap' :: Traversable (Map' k)

instance containerIMap :: ContainerI (k) (Map' k) where
  ixF (Map' (Product (Tuple (Const i) _))) = i

instance containerMap :: Ord k => Container (k) (Map k) (Map' k) where
  upZF (a :<-: z) = case extract z of
    Map' (Product (Tuple (Const i) as)) -> Map.insert i a as
  downZF as = as # mapWithIndex \i a ->
    a :<-: defer \_ -> Map' (Product (Tuple (Const i) (Map.delete i as)))

-- Container instances for datatypes defined in Basics
instance containerPair :: Container (Boolean) Basics.Pair Basics.Pair' where
  upZF (a :<-: z) = case extract z of
    Basics.Pair0 {- a -} a1 -> Basics.Pair a a1
    Basics.Pair1 a0 {- a -} -> Basics.Pair a0 a

  downZF (Basics.Pair a0 a1) = Basics.Pair (a0 :<-: defer \_ -> Basics.Pair0 {- a0 -} a1) (a1 :<-: defer \_ -> Basics.Pair1 a0 {- a1 -})

instance containerIPair :: ContainerI (Boolean) Basics.Pair' where
  ixF (Basics.Pair0 _) = false
  ixF (Basics.Pair1 _) = true

instance containerTriplet :: Container (Basics.Three) Basics.Triplet Basics.Triplet' where
  upZF (a :<-: z) = case extract z of
    Basics.Triplet0 {- a -} a1 a2 -> Basics.Triplet a a1 a2
    Basics.Triplet1 a0 {- a -} a2 -> Basics.Triplet a0 a a2
    Basics.Triplet2 a0 a1 {- a -} -> Basics.Triplet a0 a1 a

  downZF (Basics.Triplet a0 a1 a2) = Basics.Triplet (a0 :<-: defer \_ -> Basics.Triplet0 {- a0 -} a1 a2) (a1 :<-: defer \_ -> Basics.Triplet1 a0 {- a1 -} a2) (a2 :<-: defer \_ -> Basics.Triplet2 a0 a1 {- a2 -})

instance containerITriplet :: ContainerI (Basics.Three) Basics.Triplet' where
  ixF (Basics.Triplet0 _ _) = Basics.Three1
  ixF (Basics.Triplet1 _ _) = Basics.Three2
  ixF (Basics.Triplet2 _ _) = Basics.Three3

instance containerTextLitF :: Container (Natural) Basics.TextLitF Basics.TextLitF' where
  upZF (a :<-: z) = case extract z of
    Basics.TextInterp0 s {- a -} a1 -> Basics.TextInterp s a a1
    Basics.TextInterp1 s a0 a1 -> Basics.TextInterp s a0 (upZF (a :<-: pure a1))

  downZF (Basics.TextLit s) = Basics.TextLit s
  downZF (Basics.TextInterp s a0 a1) = Basics.TextInterp s (a0 :<-: defer \_ -> Basics.TextInterp0 s {- a0 -} a1) (downZF a1 <#> _contextZF' (map \z -> Basics.TextInterp1 s a0 z))

instance containerITextLitF :: ContainerI (Natural) Basics.TextLitF' where
  ixF (Basics.TextInterp0 _ _) = zero
  ixF (Basics.TextInterp1 _ _ z) = one + (ixF z)

instance containerMergeF :: Container (Basics.Three) Basics.MergeF Basics.MergeF' where
  upZF (a :<-: z) = case extract z of
    Basics.MergeF0 {- a -} a1 a2 -> Basics.MergeF a a1 a2
    Basics.MergeF1 a0 {- a -} a2 -> Basics.MergeF a0 a a2
    Basics.MergeF2 a0 a1 a2 -> Basics.MergeF a0 a1 (upZF (a :<-: pure a2))

  downZF (Basics.MergeF a0 a1 a2) = Basics.MergeF (a0 :<-: defer \_ -> Basics.MergeF0 {- a0 -} a1 a2) (a1 :<-: defer \_ -> Basics.MergeF1 a0 {- a1 -} a2) (downZF a2 <#> _contextZF' (map \z -> Basics.MergeF2 a0 a1 z))

instance containerIMergeF :: ContainerI (Basics.Three) Basics.MergeF' where
  ixF (Basics.MergeF0 _ _) = Basics.Three1
  ixF (Basics.MergeF1 _ _) = Basics.Three2
  ixF (Basics.MergeF2 _ _ z) = const Basics.Three3 (ixF z)

instance containerLetF :: Container (Basics.Three) Basics.LetF Basics.LetF' where
  upZF (a :<-: z) = case extract z of
    Basics.LetF0 s a0 a1 a2 -> Basics.LetF s (upZF (a :<-: pure a0)) a1 a2
    Basics.LetF1 s a0 {- a -} a2 -> Basics.LetF s a0 a a2
    Basics.LetF2 s a0 a1 {- a -} -> Basics.LetF s a0 a1 a

  downZF (Basics.LetF s a0 a1 a2) = Basics.LetF s (downZF a0 <#> _contextZF' (map \z -> Basics.LetF0 s z a1 a2)) (a1 :<-: defer \_ -> Basics.LetF1 s a0 {- a1 -} a2) (a2 :<-: defer \_ -> Basics.LetF2 s a0 a1 {- a2 -})

instance containerILetF :: ContainerI (Basics.Three) Basics.LetF' where
  ixF (Basics.LetF0 _ z _ _) = const Basics.Three1 (ixF z)
  ixF (Basics.LetF1 _ _ _) = Basics.Three2
  ixF (Basics.LetF2 _ _ _) = Basics.Three3

instance containerBindingBody :: Container (Boolean) Basics.BindingBody Basics.BindingBody' where
  upZF (a :<-: z) = case extract z of
    Basics.BindingBody0 s {- a -} a1 -> Basics.BindingBody s a a1
    Basics.BindingBody1 s a0 {- a -} -> Basics.BindingBody s a0 a

  downZF (Basics.BindingBody s a0 a1) = Basics.BindingBody s (a0 :<-: defer \_ -> Basics.BindingBody0 s {- a0 -} a1) (a1 :<-: defer \_ -> Basics.BindingBody1 s a0 {- a1 -})

instance containerIBindingBody :: ContainerI (Boolean) Basics.BindingBody' where
  ixF (Basics.BindingBody0 _ _) = false
  ixF (Basics.BindingBody1 _ _) = true

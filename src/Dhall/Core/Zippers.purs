module Dhall.Core.Zippers where

import Prelude

import Control.Comonad (class Comonad, class Extend, extract)
import Control.Comonad.Env (EnvT)
import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NonEmptyArray
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
import Data.Lens (Lens, Lens', Prism', Traversal', elementsOf, firstOf, iso, lens, prism', re)
import Data.Lens.Indexed (itraversed, unIndex)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromJust)
import Data.Newtype (class Newtype, over)
import Data.NonEmpty (NonEmpty(..))
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
import Dhall.Core.StrMapIsh (InsOrdStrMap(..), mkIOSM, unIOSM)
import Dhall.Core.Zippers.Merge (class Merge)
import Partial.Unsafe (unsafePartial)
import Prim.RowList as RL
import Type.Data.RowList (RLProxy(..))
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
class (Eq1 f, Eq1 f', Ord i, Merge f, Merge f', TraversableWithIndex i f, Traversable f', ContainerI i f', Functor f', Functor f) <= Container i f f' | f -> i f', f' -> i where
  upZF   :: forall x. ZF f' x  ->      f  x
  downZF :: forall x.    f  x -> f (ZF f' x)

mapWithIndexV :: forall rl is fs a b.
  RL.RowToList fs rl =>
  FunctorWithIndexVRL rl is fs =>
  (Variant is -> a -> b) -> VariantF fs a -> VariantF fs b
mapWithIndexV = mapWithIndexVRL (RLProxy :: RLProxy rl)

class FunctorWithIndexVRL rl is fs | rl -> is fs where
  mapWithIndexVRL :: forall a b. RLProxy rl ->
    (Variant is -> a -> b) -> VariantF fs a -> VariantF fs b

instance functorWithIndexVRLNil :: FunctorWithIndexVRL RL.Nil () () where
  mapWithIndexVRL _ _ = VariantF.case_

instance functorWithIndexVRLCons ::
  ( IsSymbol s
  , FunctorWithIndex i f
  , Row.Cons s (FProxy f) fs' fs
  , Row.Cons s i is' is
  , Row.Union is' is_ is
  , Row.Union fs' fs_ fs
  , FunctorWithIndexVRL rl' is' fs'
  ) => FunctorWithIndexVRL (RL.Cons s (FProxy f) rl') is fs where
  mapWithIndexVRL _ f = VariantF.on s
    (mapWithIndex (Variant.inj s >>> f) >>> VariantF.inj s)
    (mapWithIndexVRL (RLProxy :: RLProxy rl') (f <<< Variant.expand) >>> VariantF.expand)
    where s = SProxy :: SProxy s

ixFV :: forall rl is f's x.
  RL.RowToList f's rl =>
  ContainerIVRL rl is f's =>
  VariantF f's x -> Variant is
ixFV = ixFVRL (RLProxy :: RLProxy rl)

class ContainerIVRL rl is f's | rl -> is f's where
  ixFVRL :: forall x. RLProxy rl -> VariantF f's x -> Variant is

instance containerIVRLNil :: ContainerIVRL RL.Nil () () where
  ixFVRL _ = VariantF.case_

instance containerIVRLCons ::
  ( IsSymbol s
  , ContainerI i f'
  , Row.Cons s (FProxy f') f's' f's
  , Row.Cons s i is' is
  , Row.Union is' is_ is
  , ContainerIVRL rl' is' f's'
  ) => ContainerIVRL (RL.Cons s (FProxy f') rl') is f's where
  ixFVRL _ = VariantF.on s (ixF >>> Variant.inj s)
    (ixFVRL (RLProxy :: RLProxy rl') >>> Variant.expand)
    where s = SProxy :: SProxy s

upZFV :: forall rl is fs f's x.
  RL.RowToList fs rl =>
  ContainerVRL rl is fs f's =>
  ZF (VariantF f's) x -> VariantF fs x
upZFV = upZFVRL (RLProxy :: RLProxy rl)

downZFV :: forall rl is fs f's x.
  RL.RowToList fs rl =>
  ContainerVRL rl is fs f's =>
  VariantF fs x -> VariantF fs (ZF (VariantF f's) x)
downZFV = downZFVRL (RLProxy :: RLProxy rl)

class ContainerVRL rl (is :: # Type) fs f's | rl -> is fs f's where
  upZFVRL :: forall x. RLProxy rl -> ZF (VariantF f's) x -> VariantF fs x
  downZFVRL :: forall x. RLProxy rl -> VariantF fs x -> VariantF fs (ZF (VariantF f's) x)

instance containerVRLNil :: ContainerVRL RL.Nil () () () where
  upZFVRL _ (_ :<-: z) = VariantF.case_ (extract z)
  downZFVRL _ = VariantF.case_

instance containerVRLCons ::
  ( IsSymbol s
  , Functor f'
  , Container i f f'
  , Row.Cons s (FProxy f) fs' fs
  , Row.Cons s (FProxy f') f's' f's
  , Row.Cons s i is' is
  , Row.Union fs' fs_ fs
  , Row.Union f's' f's_ f's
  , ContainerVRL rl' is' fs' f's'
  ) => ContainerVRL (RL.Cons s (FProxy f) rl') is fs f's where
  upZFVRL _ (a :<-: z) = VariantF.on s
    (\z' -> upZF (a :<-: pure z') # VariantF.inj s)
    (\z' -> upZFVRL (RLProxy :: RLProxy rl') (a :<-: pure z') # VariantF.expand)
    (extract z)
    where s = SProxy :: SProxy s
  downZFVRL _ = VariantF.on s
    (downZF >>> injector (VariantF.inj s) (VariantF.inj s))
    (downZFVRL (RLProxy :: RLProxy rl') >>> injector VariantF.expand VariantF.expand)
    where s = SProxy :: SProxy s

-- Random utilities
injector :: forall f g f' g' a. Functor f => (f ~> g) -> (f' a -> g' a) -> f (ZF f' a) -> g (ZF g' a)
injector fg f'g' = (map <<< _contextZF' <<< map) f'g' >>> fg

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

-- Target an element by index
_ix :: forall i f x. TraversableWithIndex i f => Eq i => i -> Traversal' (f x) x
_ix i = unIndex $ elementsOf itraversed $ eq i

-- Lookup a zipper by its index in the functor
previewIndexZF :: forall i f f' x. Container i f f' => i -> f x -> Maybe (ZF f' x)
previewIndexZF i = firstOf (_ix i) <<< downZF

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

type Const' c = Const Void
type ConstI c = Void

instance containerConst :: Eq c => Container Void (Const c) (Const Void) where
  upZF (_ :<-: z) = case extract z of Const void -> absurd void
  downZF (Const c) = Const c

type Identity' = Const Unit
type IdentityI = Unit

instance containerIdentity :: Container Unit Identity (Const Unit) where
  upZF (a :<-: z) = case extract z of
    Const (_ :: Unit) -> Identity a
  downZF (Identity a) = Identity (a :<-: pure (Const unit))

type Coproduct' = Coproduct
type CoproductI = Either

instance containerICoproduct :: (ContainerI i f', ContainerI j g') => ContainerI (Either i j) (Coproduct f' g') where
  ixF (Coproduct (Left cf)) = Left $ ixF cf
  ixF (Coproduct (Right cg)) = Right $ ixF cg

-- Sum rule: (f + g)' = f' + g'
instance containerCoproduct :: (Eq1 f, Eq1 g, Merge f, Merge g, Functor f', Functor g', Container i f f', Container j g g') =>
  Container (Either i j) (Coproduct f g) (Coproduct f' g') where
    downZF (Coproduct (Left f)) = downZF f # injector Coproduct.left Coproduct.left
    downZF (Coproduct (Right g)) = downZF g # injector Coproduct.right Coproduct.right
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
derive newtype instance mergeProduct' :: (Merge f, Merge f', Merge g, Merge g') => Merge (Product' f f' g g')
derive newtype instance functorWithIndexProduct' ::
  ( FunctorWithIndex i f
  , FunctorWithIndex i' f'
  , FunctorWithIndex j g
  , FunctorWithIndex j' g'
  ) => FunctorWithIndex (Either (Either i' j) (Either i j')) (Product' f f' g g')
derive newtype instance foldableWithIndexProduct' ::
  ( FoldableWithIndex i f
  , FoldableWithIndex i' f'
  , FoldableWithIndex j g
  , FoldableWithIndex j' g'
  ) => FoldableWithIndex (Either (Either i' j) (Either i j')) (Product' f f' g g')
derive newtype instance traversableWithIndexProduct' ::
  ( TraversableWithIndex i f
  , TraversableWithIndex i' f'
  , TraversableWithIndex j g
  , TraversableWithIndex j' g'
  ) => TraversableWithIndex (Either (Either i' j) (Either i j')) (Product' f f' g g')
instance containerProduct' ::
  ( Container i f f', Eq1 f, Traversable f, Merge f
  , Container i' f' f'', Functor f''
  , Container j g g', Eq1 g, Traversable g, Merge g
  , Container j' g' g'', Functor g''
  ) => Container (Either (Either i' j) (Either i j')) (Product' f f' g g')
    (Coproduct (Product' f' f'' g g') (Product' f f' g' g''))
  where
  upZF = Product' <<< upZF
  downZF = over Product' downZF
type ProductI = Either

instance containerIProduct :: (ContainerI i f', ContainerI j g') => ContainerI (Either i j) (Product' f f' g g') where
  ixF (Product' (Coproduct (Left (Product (Tuple cf _))))) = Left $ ixF cf
  ixF (Product' (Coproduct (Right (Product (Tuple _ cf))))) = Right $ ixF cf

instance containerProduct :: (Eq1 f, Eq1 g, Functor f', Merge f, Merge g, Functor g', Traversable f, Traversable g, Container i f f', Container j g g') =>
  Container (Either i j) (Product f g) (Product' f f' g g') where
    downZF (Product (Tuple f g)) = Product $ Tuple
      (downZF f <#> _contextZF \cf ->
        Product' (Coproduct (Left (Product (Tuple cf g)))))
      (downZF g <#> _contextZF \cg ->
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
derive newtype instance mergeCompose' :: (Merge f', Traversable f', Merge g, Merge g') => Merge (Compose' f' g g')
derive newtype instance functorWithIndexCompose' ::
  ( FunctorWithIndex i' f'
  , FunctorWithIndex j g
  , FunctorWithIndex j' g'
  ) => FunctorWithIndex (Either (Tuple i' j) j') (Compose' f' g g')
derive newtype instance foldableWithIndexCompose' ::
  ( FoldableWithIndex i' f'
  , FoldableWithIndex j g
  , FoldableWithIndex j' g'
  ) => FoldableWithIndex (Either (Tuple i' j) j') (Compose' f' g g')
derive newtype instance traversableWithIndexCompose' ::
  ( TraversableWithIndex i' f'
  , TraversableWithIndex j g
  , TraversableWithIndex j' g'
  ) => TraversableWithIndex (Either (Tuple i' j) j') (Compose' f' g g')
instance containerCompose' ::
  ( Container i' f' f'', Eq1 f', Functor f'', Traversable f', Merge f'
  , Container j g g', Eq1 g, Traversable g, Merge g
  , Container j' g' g'', Functor g''
  ) => Container (Either (Tuple i' j) j') (Compose' f' g g')
    (Product' (Compose f' g) (Compose' f'' g g') g' g'')
  where
  upZF = Compose' <<< upZF
  downZF = over Compose' downZF
type ComposeI = Tuple

instance containerICompose :: (ContainerI i f', ContainerI j g') =>
  ContainerI (Tuple i j) (Compose' f' g g') where
    ixF (Compose' (Product (Tuple (Compose f'g) g'))) = Tuple (ixF f'g) (ixF g')

instance containerCompose :: (Eq1 f, Eq1 g, Traversable f, Merge f, Merge g, Functor f', Functor g', Traversable g, Container i f f', Container j g g') =>
  Container (Tuple i j) (Compose f g) (Compose' f' g g') where
    downZF (Compose fg) = Compose $ downZF fg <#> \(g :<-: f'g) ->
      downZF g <#> _contextZF \a ->
        Compose' (Product.product (Compose (extract f'g)) a)
    upZF (a :<-: z) = case extract z of
      Compose' (Product (Tuple (Compose f'g) g')) -> Compose $ upZF $
        upZF (a :<-: pure g') :<-: pure f'g

type Maybe' = Const Unit
type MaybeI = Unit

instance containerMaybe :: Container Unit Maybe (Const Unit) where
  upZF (a :<-: z) = case extract z of
    Const (_ :: Unit) -> Just a
  downZF Nothing = Nothing
  downZF (Just a) = Just (a :<-: pure (Const unit))

type Either' c = Const Unit
type EitherI = Unit

instance containerEither :: (Eq c) => Container Unit (Either c) (Const Unit) where
  upZF (a :<-: z) = case extract z of
    Const (_ :: Unit) -> Right a
  downZF (Left c) = Left c
  downZF (Right a) = Right (a :<-: pure (Const unit))

type Tuple' c = Const c
type TupleI c = Unit

instance containerTuple :: (Eq c) => Container Unit (Tuple c) (Const c) where
  upZF (a :<-: z) = case extract z of
    Const c -> Tuple c a
  downZF (Tuple c a) = Tuple c (a :<-: pure (Const c))

newtype NonEmpty' f f' a = NonEmpty' (Coproduct f (Product Identity f') a)
derive instance newtypeNonEmpty' :: Newtype (NonEmpty' f f' a) _
derive newtype instance eqNonEmpty' :: (Eq1 f, Eq1 f', Eq a) => Eq (NonEmpty' f f' a)
derive newtype instance ordNonEmpty' :: (Ord1 f, Ord1 f', Ord a) => Ord (NonEmpty' f f' a)
derive newtype instance eq1NonEmpty' :: (Eq1 f, Eq1 f') => Eq1 (NonEmpty' f f')
derive newtype instance ord1NonEmpty' :: (Ord1 f, Ord1 f') => Ord1 (NonEmpty' f f')
derive newtype instance functorNonEmpty' :: (Functor f, Functor f') => Functor (NonEmpty' f f')
derive newtype instance foldableNonEmpty' :: (Foldable f, Foldable f') => Foldable (NonEmpty' f f')
derive newtype instance traversableNonEmpty' :: (Traversable f, Traversable f') => Traversable (NonEmpty' f f')
derive newtype instance mergeNonEmpty' :: (Merge f, Merge f') => Merge (NonEmpty' f f')

instance containerNonEmpty :: (Eq1 f, Traversable f, Merge f, Functor f', Container i f f') => Container (Maybe i) (NonEmpty f) (NonEmpty' f f') where
  upZF (a :<-: z) = case extract z of
    NonEmpty' (Coproduct (Left fa)) -> NonEmpty a fa
    NonEmpty' (Coproduct (Right (Product (Tuple (Identity a0) f'a)))) ->
      NonEmpty a0 (upZF (a :<-: pure f'a))

  downZF (NonEmpty a0 fa) = NonEmpty
    (a0 :<-: defer \_ -> NonEmpty' (Coproduct (Left fa)))
    (downZF fa <#> _contextZF' (map \f'a -> NonEmpty' (Coproduct (Right (Product (Tuple (Identity a0) f'a))))))

instance containerINonEmpty :: ContainerI i f' => ContainerI (Maybe i) (NonEmpty' f f') where
  ixF (NonEmpty' (Coproduct (Left _))) = Nothing
  ixF (NonEmpty' (Coproduct (Right (Product (Tuple _ f'a))))) = Just (ixF f'a)

newtype Array' a = ArrayN (Product Array Array a)
derive instance newtypeArray' :: Newtype (Array' a) _
derive newtype instance eqArray' :: Eq a => Eq (Array' a)
derive newtype instance ordArray' :: Ord a => Ord (Array' a)
derive newtype instance eq1Array' :: Eq1 Array'
derive newtype instance ord1Array' :: Ord1 Array'
derive newtype instance functorArray' :: Functor Array'
derive newtype instance foldableArray' :: Foldable Array'
derive newtype instance traversableArray' :: Traversable Array'
derive newtype instance functorWithIndexArray' :: FunctorWithIndex (Either Int Int) Array'
derive newtype instance foldableWithIndexArray' :: FoldableWithIndex (Either Int Int) Array'
derive newtype instance traversableWithIndexArray' :: TraversableWithIndex (Either Int Int) Array'
derive newtype instance mergeArray' :: Merge Array'
instance containerArray' :: Container (Either Int Int) Array' (Product' Array Array' Array Array') where
  upZF = ArrayN <<< upZF
  downZF = over ArrayN downZF
type ArrayI = Int -- unfortunately

arrayN :: forall a. Array a -> Array a -> Array' a
arrayN prev next = ArrayN (Product (Tuple prev next))

instance containerIArray :: ContainerI (Int) Array' where
  ixF (ArrayN (Product (Tuple prev _))) = Array.length prev

instance containerArray :: Container (Int) Array Array' where
  upZF (a :<-: z) = case extract z of
    ArrayN (Product (Tuple prev next)) -> prev <> [a] <> next
  downZF as = let l = Array.length as in as # mapWithIndex \i a ->
    a :<-: defer \_ -> arrayN (Array.slice 0 i as) (Array.slice (i+1) l as)

instance containerNonEmptyArray :: Container (Int) NonEmptyArray Array' where
  upZF (a :<-: z) = case extract z of
    ArrayN (Product (Tuple prev next)) ->
      NonEmptyArray.appendArray (NonEmptyArray.snoc' prev a) next
  downZF as = let l = NonEmptyArray.length as in as # mapWithIndex \i a ->
    a :<-: defer \_ -> arrayN (NonEmptyArray.slice 0 i as) (NonEmptyArray.slice (i+1) l as)

newtype Map' k a = Map' (Product (Const k) (Map k) a)
derive instance newtypeMap' :: Newtype (Map' k a) _
derive newtype instance eqMap' :: (Eq k, Eq a) => Eq (Map' k a)
derive newtype instance ordMap' :: (Ord k, Ord a) => Ord (Map' k a)
derive newtype instance eq1Map' :: Eq k => Eq1 (Map' k)
derive newtype instance ord1Map' :: Ord k => Ord1 (Map' k)
derive newtype instance functorMap' :: Functor (Map' k)
derive newtype instance foldableMap' :: Foldable (Map' k)
derive newtype instance traversableMap' :: Traversable (Map' k)
derive newtype instance functorWithIndexMap' :: FunctorWithIndex (Either Void k) (Map' k)
derive newtype instance foldableWithIndexMap' :: FoldableWithIndex (Either Void k) (Map' k)
derive newtype instance traversableWithIndexMap' :: TraversableWithIndex (Either Void k) (Map' k)
derive newtype instance mergeMap' :: Ord k => Merge (Map' k)
instance containerMap' :: Ord k => Container (Either Void k) (Map' k) (Product' (Const k) (Const Void) (Map k) (Map' k)) where
  upZF = Map' <<< upZF
  downZF = over Map' downZF
type MapI k = k

instance containerIMap :: ContainerI (k) (Map' k) where
  ixF (Map' (Product (Tuple (Const i) _))) = i

instance containerMap :: Ord k => Container (k) (Map k) (Map' k) where
  upZF (a :<-: z) = case extract z of
    Map' (Product (Tuple (Const i) as)) -> Map.insert i a as
  downZF as = as # mapWithIndex \i a ->
    a :<-: defer \_ -> Map' (Product (Tuple (Const i) (Map.delete i as)))

newtype InsOrdStrMap' a = InsOrdStrMap' (Product (Const String) (Product InsOrdStrMap InsOrdStrMap) a)
derive instance newtypeInsOrdStrMap' :: Newtype (InsOrdStrMap' a) _
derive newtype instance eqInsOrdStrMap' :: Eq a => Eq (InsOrdStrMap' a)
derive newtype instance ordInsOrdStrMap' :: Ord a => Ord (InsOrdStrMap' a)
derive newtype instance eq1InsOrdStrMap' :: Eq1 InsOrdStrMap'
derive newtype instance ord1InsOrdStrMap' :: Ord1 InsOrdStrMap'
derive newtype instance functorInsOrdStrMap' :: Functor InsOrdStrMap'
derive newtype instance foldableInsOrdStrMap' :: Foldable InsOrdStrMap'
derive newtype instance traversableInsOrdStrMap' :: Traversable InsOrdStrMap'
derive newtype instance mergeInsOrdStrMap' :: Merge InsOrdStrMap'
derive newtype instance functorWithIndexInsOrdStrMap' :: FunctorWithIndex (Either Void (Either String String)) InsOrdStrMap'
derive newtype instance foldableWithIndexInsOrdStrMap' :: FoldableWithIndex (Either Void (Either String String)) InsOrdStrMap'
derive newtype instance traversableWithIndexInsOrdStrMap' :: TraversableWithIndex (Either Void (Either String String)) InsOrdStrMap'
instance containerInsOrdStrMap' :: Container
  (Either Void (Either String String)) InsOrdStrMap'
  (Product' (Const String) (Const Void)
    (Product InsOrdStrMap InsOrdStrMap) (Product' InsOrdStrMap InsOrdStrMap' InsOrdStrMap InsOrdStrMap')
  ) where
  upZF = InsOrdStrMap' <<< upZF
  downZF = over InsOrdStrMap' downZF
type InsOrdStrMapI = String

instance containerIIOSM :: ContainerI String InsOrdStrMap' where
  ixF (InsOrdStrMap' (Product (Tuple (Const k) _))) = k

instance containerIOSM :: Container String InsOrdStrMap InsOrdStrMap' where
  upZF (a :<-: z) = case extract z of
    InsOrdStrMap' (Product (Tuple (Const k) (Product (Tuple prev next)))) ->
      mkIOSM (unIOSM prev <> [Tuple k a] <> unIOSM next)
  downZF (InsOrdStrMap (Compose as)) = mkIOSM $ as #
    let l = Array.length as in
    mapWithIndex \i (Tuple k a) -> Tuple k $
      a :<-: defer \_ ->
        let
          prev = mkIOSM $ Array.slice 0 i as
          next = mkIOSM $ Array.slice (i+1) l as
        in InsOrdStrMap' (Product (Tuple (Const k) (Product (Tuple prev next))))

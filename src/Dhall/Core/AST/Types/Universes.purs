module Dhall.Core.AST.Types.Universes where


import Prelude

import Control.Alternative (empty)
import Data.Array as Array
import Data.Foldable (all, foldMap, oneOfMap)
import Data.FoldableWithIndex (foldMapWithIndex)
import Data.List (List)
import Data.List as List
import Data.Map (SemigroupMap(..))
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Newtype (class Newtype, over)
import Data.NonEmpty (NonEmpty(..))
import Data.Ord.Max (Max(..))
import Data.Semigroup.Foldable (fold1)
import Data.Set (Set)
import Data.Set as Set
import Data.String as String
import Data.Tuple (Tuple(..))


-- | Inject `Tail` into `Const`
upure :: Tail -> Const
upure = Universes <<< SemigroupMap <<< Map.singleton Set.empty

-- | `uconst 0`, the zero constant, the level for `Type`
uempty :: Const
uempty = Universes mempty

-- | Turn an integer into a constant, with negative integers being truncated to zero.
uconst :: Int -> Const
uconst i | i <= 0 = uempty
uconst i = upure $ Tail mempty (Max i)

-- | A variable level, shifting by the specified integer amount (may be negative, but very rarely).
uvarS :: String -> Int -> Const
uvarS "" i = uconst i
uvarS v i = upure $ Tail (SemigroupMap (Map.singleton v (Max i))) (Max i)

-- | A plain variable, no shifting.
uvar :: String -> Const
uvar = flip uvarS 0

-- | The universe level constant for `Type` (zero).
uType = uconst 0 :: Const
-- | The universe level constant for `Kind` (one).
uKind = uconst 1 :: Const
-- | The universe level constant for `Sort` (two).
uSort = uconst 2 :: Const

-- | Shift a level by a constant amount (may be negative).
-- | For example, `ushift (uvar u) d = uvarS u d`.
ushift :: Const -> Int -> Const
ushift u d | u == uempty = uconst d
ushift (Universes cs) d = Universes $ cs <#> \(Tail us (Max ui)) ->
  Tail (us <#> \(Max u) -> Max (u + d)) (Max (ui + d))

infix 6 ushift as ^+

-- Defining equations
-- (x; 0) := 0
-- (x; y+1) := (x, y+1)

-- Axiomatization
-- (x, y) >= (x; y)
-- (x; y) >= y
-- 0 >= y ==> 0 >= (x; y)
-- (x; y) > 0 ==> (x; y) >= (x, y)
-- (x; y)+c == (x+c; y), y+c

-- 0 >= y ==> 0 >= (x; y)
-- 0 == y ==> 0 == (x; y)
-- 0 == (x; 0)
-- (x; 0) == 0.

-- (x; y) >= y
-- y > 0 ==> (x; y) > 0
-- y > 0 ==> (x; y) >= (x, y)
-- (x, y) >= (x; y)
-- y > 0 ==> (x; y) == (x, y)
-- (x; y+1) == (x, y+1).

-- Defining equations 2
-- (x; ^0) := 0
-- (x; ^y+1) := x
-- (x; y) := (x; ^y), y

-- Axiomatization 2
-- x >= (x; ^y)
-- 0 >= y ==> 0 >= (x; ^y)
-- y > 0 ==> (x; ^y) >= x
-- thus: (x; ^y) > 0 ==> (x; ^y) >= x

-- 0 >= y ==> 0 >= (x; ^y)
-- 0 == y ==> 0 == (x; ^y)
-- (x; ^0) = 0.

-- x >= (x; ^y)
-- y > 0 ==> (x; ^y) >= x
-- y > 0 ==> (x; ^y) == x
-- (x; ^y+1) == x.

-- | Normal forms for predicative universe expressions.
data Tail = Tail (SemigroupMap String (Max Int)) (Max Int)
derive instance eqTail :: Eq Tail
derive instance ordTail :: Ord Tail
instance semigroupTail :: Semigroup Tail where
  append (Tail as a) (Tail bs b) = Tail (as <> bs) (a <> b)
newtype Const = Universes (SemigroupMap (Set String) Tail)
derive instance newtypeConst :: Newtype Const _
derive instance eqConst :: Eq Const
derive instance ordConst :: Ord Const
instance semigroupConst :: Semigroup Const where
  append (Universes az) (Universes bz) = Universes (az <> bz)
instance showConst :: Show Const where
  show (Universes uz) = "(Universe " <> shown <> ")"
    where
      findKey k = case findChainIn (Universes uz) k of
        Just js -> js
        Nothing -> pure $ "^" <> String.joinWith "^" (Array.fromFoldable k)
      args = foldMapWithIndex (map pure <<< renderItems <<< findKey) uz
      renderItems List.Nil t = renderTail t
      renderItems js t =
        "(" <> String.joinWith "; " ([renderTail t] <> Array.fromFoldable js) <> ")"
      renderTail (Tail (SemigroupMap us) (Max u)) =
        let c = if Just (Max u) == foldMap Just us then [] else [show u] in
        String.joinWith ", " $ c <> foldMapWithIndex renderItem us
      renderItem i (Max v) = [i <> (if v == zero then "" else "+" <> show v)]
      shown = case args of
        _ -> "(" <> String.joinWith ", " args <> ")"

-- | Get the `Tail` of the `Const`, i.e. what it is without any hypotheticals.
getTail :: Const -> Tail
getTail = fromMaybe (Tail mempty (Max zero)) <<<
  \(Universes (SemigroupMap m)) -> Map.lookup Set.empty m

-- | Is the `Const` in the image of `upure`.
onlyTail :: Const -> Boolean
onlyTail (Universes (SemigroupMap m)) = Set.subset (Map.keys m) $ Set.singleton Set.empty

-- | Get the variables mentioned in a `Tail`.
getVars :: Tail -> Set String
getVars (Tail (SemigroupMap us) _) = Map.keys us

-- | If the `Tail` is only a constant, return it, otherwise nothing.
onlyConst :: Tail -> Maybe Int
onlyConst (Tail (SemigroupMap us) (Max u)) =
  if Map.isEmpty us then Just u else Nothing

-- | If the `Tail` is only an *unshifted* variable, return it, otherwise nothing.
onlyVar :: Tail -> Maybe String
onlyVar (Tail (SemigroupMap us) (Max u)) =
  if u /= zero || Map.size us /= one then Nothing else
    Map.findMin us >>= \{ key, value } ->
      if value /= Max zero then Nothing else Just key

-- | If the `Tail` is only a possibly shifted variable, return it, otherwise nothing.
onlyVarS :: Tail -> Maybe (Tuple String Int)
onlyVarS (Tail (SemigroupMap us) (Max u)) =
  if Map.size us /= one then Nothing else
    Map.findMin us >>= \{ key, value: Max value } ->
      if u == value then Just (Tuple key value) else Nothing

-- | Internal helper for printing. Given a `Const`, find a ordering of the
-- | variables given as `Set String` that realize the evidence that this
-- | expression can be written with `imax`, not `if`.
findChainIn :: Const -> Set String -> Maybe (List String)
findChainIn (Universes (SemigroupMap top)) = go List.Nil where
  go x vars | Set.isEmpty vars = Just x
  go x vars =
    let
      xx = Set.fromFoldable x
      incl = top # foldMapWithIndex \ks (Tail (SemigroupMap vs) _) ->
        if Set.subset ks xx then Map.keys vs else mempty
    in vars # oneOfMap \var ->
      if not Set.member var incl then empty else
        go (List.Cons var x) (Set.delete var vars)

-- | Normalize a constant. This has two steps: we first normalize each `Tail`
-- | in the constant, and then we remove redundancy: for each hypothetical,
-- | remove information that is already known from smaller hypotheticals
-- | (see `reduceBySelf`).
normalizeConst :: Const -> Const
normalizeConst (Universes uz) =
  Universes uz' # reduceBySelf
    where
      uz' = map normalizeTail uz
      normalizeTail (Tail us u) = Tail us
        (fold1 (NonEmpty u us) <> Max zero)

-- | Construct a `Tail` from a set of variables (unshifted).
varsTail :: Set String -> Tail
varsTail vars =
  let kv = Array.fromFoldable vars <#> \v -> Tuple v (Max zero)
  in Tail (SemigroupMap (Map.fromFoldable kv)) (Max zero)

-- | Construct a `Const` from a set of variables (unshifted).
varsConst :: Set String -> Const
varsConst = upure <<< varsTail

-- | Evaluate a `Const` at the hypothetical of type `Set String`.
-- |
-- | This function is central to the interpretation of `Const`: each
-- | hypothetical cannot be considered in isolation, but must be considered in
-- | the context of what hypotheticals are already satisfied when this
-- | hypothetical is satisfied.
foundAt :: Set String -> Const -> Tail
foundAt vars (Universes c) =
  (maybe <*> append) (varsTail vars) $
    c # foldMapWithIndex \ks v ->
      if Set.subset ks vars then Just v else mempty

-- | Evaluate a `Const` _below_ the hypothetical: everything that is already
-- | implied at that point, though excluding the actual value at the
-- | hypothetical itself.
foundBy :: Set String -> Const -> Tail
foundBy vars (Universes c) =
  (maybe <*> append) (varsTail vars) $
    c # foldMapWithIndex \ks v ->
      if Set.properSubset ks vars then Just v else mempty

-- | Remove information that is implied already.
-- | This is used for normalizing constants.
reduceBy :: Tail -> Tail -> Maybe Tail
reduceBy (Tail (SemigroupMap source) (Max sv)) (Tail (SemigroupMap target) (Max tv)) =
  let
    target' = target # Map.mapMaybeWithKey \k v ->
      case Map.lookup k source of
        Just v2 | v2 >= v -> Nothing
        _ -> Just v
  in if Map.isEmpty target' && sv >= tv then Nothing
    else Just (Tail (SemigroupMap target') (Max tv <> Max sv))

-- | Reduce by a different constant.
reduceByConst :: Const -> Const -> Const
reduceByConst source = over Universes $ over SemigroupMap $
  Map.mapMaybeWithKey \ks -> reduceBy (foundAt ks source)

-- | Reduce by itself.
reduceBySelf :: Const -> Const
reduceBySelf source = (_ $ source) $ over Universes $ over SemigroupMap $
  Map.mapMaybeWithKey \ks -> reduceBy (foundBy ks source)

-- | Remove information that is strictly implied already.
-- | This is used when checking consistency of `GESolver`, where each key
-- | is reduced by the value it is requested to be greater than or equal to.
reduceBy' :: Tail -> Tail -> Maybe Tail
reduceBy' (Tail (SemigroupMap source) (Max sv)) (Tail (SemigroupMap target) (Max tv)) =
  let
    target' = target # Map.mapMaybeWithKey \k v ->
      case Map.lookup k source of
        Just v2 | v2 > v -> Nothing
        _ -> Just v
  in if Map.isEmpty target' && sv > tv then Nothing
    else Just $ Tail (SemigroupMap target') $
      if sv <= tv then Max tv else
        ((maybe <*> append) (Max zero)) (foldMap Just target')

-- | Remove information that is strictly implied already.
reduceByConst' :: Const -> Const -> Const
reduceByConst' source = over Universes $ over SemigroupMap $
  Map.mapMaybeWithKey \ks -> reduceBy' (foundAt ks source)

-- | Can this expression ever be zero?
zeroable :: Const -> Boolean
zeroable = getTail >>> \(Tail us (Max u)) ->
  u <= zero && all (\(Max v) -> v <= zero) us

-- | The set of variables that need to be zero for this `Const` to be zero.
-- FIXME: over-approximation due to imax/if discrepancy?
skim :: Const -> Set String
skim (Universes (SemigroupMap uz)) =
  uz # foldMapWithIndex \k (Tail (SemigroupMap us) _) ->
    if Set.isEmpty k then Map.keys us else k

-- | The fundamental operation that `Const` introduces above `Tail`.
imax :: Const -> Const -> Const
imax (Universes (SemigroupMap us)) v | zeroable v
  = (maybe <*> append) v $
    skim v # foldMap \k ->
      us # foldMapWithIndex \ks u ->
        Just $ Universes $ SemigroupMap $ Map.singleton (Set.insert k ks) u
imax u v = u <> v

infixl 4 imax as ^<

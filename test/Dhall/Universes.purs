module Dhall.Test.Universes where

import Dhall.TypeCheck.UniSolver (GESolver(..), Rel(..), close, closure, compareConst, normalizeConst, (+<=))
import Prelude

import Control.Monad.Writer (Writer, WriterT(..), tell)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.FoldableWithIndex (forWithIndex_)
import Data.Identity (Identity(..))
import Data.Map (SemigroupMap(..))
import Data.Map as Map
import Data.Maybe (Maybe(..), isNothing)
import Data.Ord.Max (Max(..))
import Data.Tuple (Tuple(..))
import Dhall.Core (Const(..), Pair)
import Effect (Effect)
import Effect.Console (log)

mkU :: Array (Tuple String Int) -> Int -> Const
mkU us u = normalizeConst $ Universes (Map.SemigroupMap (Map.fromFoldable (map (map Max) us))) (Max u)

showU :: Const -> String
-- showU u = show u
showU (Universes (SemigroupMap us) (Max u)) = "mkU " <> show (Map.toUnfoldable (map (\(Max v) -> v) us) :: Array _) <> " " <> show u

x = mkU [Tuple "x" 0] 0 :: Const
y = mkU [Tuple "y" 0] 0 :: Const
z = mkU [Tuple "z" 0] 0 :: Const
z2 = mkU [Tuple "z" 2] 2 :: Const
xy = mkU [Tuple "x" 0, Tuple "y" 0] 0 :: Const
xy1 = mkU [Tuple "x" 0, Tuple "y" 1] 1 :: Const
x2y = mkU [Tuple "x" 2, Tuple "y" 0] 2 :: Const

assertEq :: forall a. Eq a => Show a => String -> a -> a -> Effect Unit
assertEq _ a b | a == b = pure unit
assertEq msg a b = do
  log msg
  log ("  " <> show a)
  log ("  " <> show b)

shiftLEAssert :: Const -> Const -> Maybe (Max Int) -> Effect Unit
shiftLEAssert c1 c2 r | (c1 +<= c2) == r = pure unit
shiftLEAssert c1 c2 r = do
  log "Expected"
  log ("  " <> showU c1 <> " +<= " <> showU c2)
  log "To be"
  log ("  " <> show r)
  log "Instead of"
  log ("  " <> show (c1 +<= c2))

infix 5 shiftLEAssert as !+<=

infix 1 identity as ===

compareConstAssert :: Const -> Const -> Rel -> Effect Unit
compareConstAssert c1 c2 r | compareConst c1 c2 == r = pure unit
compareConstAssert c1 c2 r = do
  log "Expected"
  log ("  " <> showU c1 <> " <=> " <> showU c2)
  log "To be"
  log ("  " <> show r)
  log "Instead of"
  log ("  " <> show (c1 `compareConst` c2))

infix 5 compareConstAssert as !<=>

closure' :: Int -> GESolver -> Maybe (Either (Pair Const) GESolver)
closure' gas _ | gas <= 0 = Nothing
closure' gas s =
  case close s of
    Left e -> Just (Left e)
    Right s' | s' == s -> Just (Right s)
    Right s' -> closure' (gas-1) s'

addToSolver :: Const -> Const -> Writer (SemigroupMap Const Const) Unit
addToSolver = map (tell <<< SemigroupMap) <<< Map.singleton

infix 2 addToSolver as !>=

consistent :: Writer (SemigroupMap Const Const) Unit -> Effect Unit
consistent (WriterT (Identity (Tuple _ (SemigroupMap constraints)))) = do
  let solver = GESolver constraints
  let solved = closure solver
  when (isNothing solved) do
    log "Was inconsistent"

inconsistent :: Writer (SemigroupMap Const Const) Unit -> Effect Unit
inconsistent (WriterT (Identity (Tuple _ (SemigroupMap constraints)))) = do
  let solver = GESolver constraints
  let solved = closure solver
  for_ solved \(GESolver solution) -> do
    log "Was consistent:"
    forWithIndex_ solution \i v -> do
      log ("  " <> showU i <> " !>= " <> showU v)

main :: Effect Unit
main = do
  xy1 !+<= x2y === Just (Max 1)
  x2y !+<= xy1 === Just (Max 2)
  x !+<= xy1 === Just (Max 0)
  xy1 !+<= x === Nothing
  z2 !+<= z === Just (Max 2)
  z !+<= z2 === Just (Max (-2))

  xy1 !<=> x2y === RUN
  z !<=> z2 === ALT
  mkU [] 0 !<=> z2 === ALT
  x !<=> x2y === ALT
  y !<=> x2y === HLE
  mkU [Tuple "x" 0] 5 !<=> x === HGE
  mkU [Tuple "x" 1] 5 !<=> x === AGT
  mkU [Tuple "x" 1] 3 !<=> mkU [Tuple "x" 0] 3 === HGE

  mkU [(Tuple "x" 2),(Tuple "y" 2),(Tuple "z" 2)] 0 !<=> mkU [(Tuple "x" 0),(Tuple "y" 0),(Tuple "z" 2)] 2 === HGE

  consistent do z2 !>= z
  inconsistent do z !>= z2
  inconsistent do
    z !>= xy
    xy !>= z2
  consistent do
    z2 !>= xy
    xy !>= z

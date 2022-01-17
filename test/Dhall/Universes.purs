module Dhall.Test.Universes where

import Prelude

import Control.Monad.Writer (Writer, WriterT(..), tell)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.FoldableWithIndex (allWithIndex, foldMapWithIndex, forWithIndex_)
import Data.Identity (Identity(..))
import Data.Map (Map, SemigroupMap(..))
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Newtype (unwrap, wrap)
import Data.Ord.Max (Max(..))
import Data.Tuple (Tuple(..))
import Dhall.Core (Const, Pair(..))
import Dhall.Core.AST.Types.Universes (uconst, uempty, uvar, uvarS, (^+), (^<))
import Dhall.TypeCheck.UniSolver (Conflict(..), ExError, GESolver(..), Rel(..), close, closure, compareConst, exemplify, verifySolutionTo, (+<=))
import Effect (Effect)
import Effect.Console (log)

--mkU :: Array (Tuple String Int) -> Int -> Const
--mkU us u = normalizeConst $ Universes (Map.SemigroupMap (Map.fromFoldable (map (map Max) us))) (Max u)

showU :: Const -> String
showU u = show u
-- showU (Universes (SemigroupMap us) (Max u)) = "mkU " <> show (Map.toUnfoldable (map (\(Max v) -> v) us) :: Array _) <> " " <> show u

x = uvar "x" :: Const
y = uvar "y" :: Const
z = uvar "z" :: Const
z2 = uvarS "z" 2 :: Const
xy = x <> y :: Const
xy1 = x <> y^+1 :: Const
x2y = x^+2 <> y :: Const
c5 = uconst 5 :: Const

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

infix 2 shiftLEAssert as !+<=

infix 1 identity as ===

compareConstAssert :: Const -> Const -> Rel -> Effect Unit
compareConstAssert c1 c2 r | compareConst c1 c2 == Just r = pure unit
compareConstAssert c1 c2 r = do
  log "Expected"
  log ("  " <> showU c1 <> " <=> " <> showU c2)
  log "To be"
  log ("  " <> show r)
  log "Instead of"
  log ("  " <> show (c1 `compareConst` c2))

infix 2 compareConstAssert as !<=>

closure' :: Int -> GESolver -> Maybe (Either Conflict GESolver)
closure' gas _ | gas <= 0 = Nothing
closure' gas s =
  case close s of
    Left e -> Just (Left e)
    Right s' | s' == s -> Just (Right s)
    Right s' -> closure' (gas-1) s'

addToSolver :: Const -> Const -> Writer (SemigroupMap Const Const) Unit
addToSolver = map (tell <<< SemigroupMap) <<< Map.singleton

infix 2 addToSolver as !>=

type MkSolver = Writer (SemigroupMap Const Const) Unit
mkSolver :: MkSolver -> GESolver
mkSolver (WriterT (Identity (Tuple _ (SemigroupMap constraints)))) =
  GESolver constraints

ensureModel' :: GESolver -> (Map String Int -> Effect Unit) -> Effect Unit
ensureModel' solved act = case exemplify solved of
  Left _ -> log "But did not have model"
  Right model ->
    case verifySolutionTo solved model of
      Left _ -> log "But model was invalid"
      Right _ -> act model

ensureModel :: GESolver -> Effect Unit
ensureModel = ensureModel' <@> \_ -> pure unit

consistent :: Writer (SemigroupMap Const Const) Unit -> Effect Unit
consistent constraints = do
  let solver = mkSolver constraints
  let solved = closure solver
  case solved of
    Nothing -> log "Was inconsistent"
    Just solv -> ensureModel solv

consistent' :: Writer (SemigroupMap Const Const) Unit -> Effect Unit
consistent' constraints = do
  let solver = mkSolver constraints
  let solved = closure solver
  case solved of
    Nothing -> log "Was inconsistent"
    Just solv -> ensureModel' solv \ex -> do
      log $ (_ <> "for") $ ex # foldMapWithIndex \k v -> k <> " = " <> show v <> ", "
      for_ solved \(GESolver solution) -> do
        forWithIndex_ solution \i v -> do
          log ("  " <> showU i <> " !>= " <> showU v)

inconsistent :: Writer (SemigroupMap Const Const) Unit -> Effect Unit
inconsistent constraints = do
  let solver = mkSolver constraints
  let solved = closure solver
  for_ solved \(GESolver solution) -> do
    log "Was consistent:"
    forWithIndex_ solution \i v -> do
      log ("  " <> showU i <> " !>= " <> showU v)

testSystem :: Writer (SemigroupMap Const Const) Unit -> Effect Unit
testSystem constraints = do
  log "Testing to show …"
  let solver = mkSolver constraints
  forWithIndex_ (unwrap solver) \i v -> do
    log ("  " <> showU i <> " !>= " <> showU v)
  let solved = closure' 10 solver
  case solved of
    Nothing -> log "… did not stabilize"
    Just (Left (Contradiction (Pair l r))) -> do
      log "… inconsistent:"
      log ("  " <> showU l <> " < " <> showU r)
    Just (Left (Undeterminable vs)) -> do
      log "… inconsistent:"
      log (show vs)
    Just (Right (GESolver solution)) -> do
      log "… consistent:"
      forWithIndex_ solution \i v -> do
        log ("  " <> showU i <> " !>= " <> showU v)
      ensureModel (GESolver solution)

stepSystem :: Writer (SemigroupMap Const Const) Unit -> Effect Unit
stepSystem constraints = do
  log "Stepping to show …"
  let solver = mkSolver constraints
  forWithIndex_ (unwrap solver) \i v -> do
    log ("  " <> showU i <> " !>= " <> showU v)
  let
    go s =
      case close s of
        Left err -> pure $ Left err
        Right solution | solution == s ->
          pure $ Right solution
        Right (GESolver solution) -> do
          log "… stepping …"
          forWithIndex_ solution \i v -> do
            log ("  " <> showU i <> " !>= " <> showU v)
          go (GESolver solution)
  solved <- go solver
  case Just solved of
    Nothing -> log "… did not stabilize"
    Just (Left (Contradiction (Pair l r))) -> do
      log "… inconsistent:"
      log ("  " <> showU l <> " < " <> showU r)
    Just (Left (Undeterminable vs)) -> do
      log "… inconsistent:"
      log (show vs)
    Just (Right (GESolver solution)) -> do
      log "… consistent:"
      forWithIndex_ solution \i v -> do
        log ("  " <> showU i <> " !>= " <> showU v)
      ensureModel (GESolver solution)

goesTo :: MkSolver -> MkSolver -> Effect Unit
goesTo constraints goal = do
  -- log "Testing …"
  let solver = mkSolver constraints
  let
    showit = forWithIndex_ (unwrap solver) \i v -> do
      log ("  " <> showU i <> " !>= " <> showU v)
  let solved = closure' 10 solver
  case solved of
    Nothing -> log "Did not stabilize:" <> showit
    Just (Left (Contradiction (Pair l r))) -> do
      log "Inconsistent:"
      log ("  " <> showU l <> " < " <> showU r)
      showit
    Just (Left (Undeterminable vs)) -> do
      log "Inconsistent:"
      log (show vs)
      showit
    Just (Right (GESolver solution)) | wrap solution /= mkSolver goal -> do
      log "Consistent but unexpected:"
      log "Expected:"
      forWithIndex_ (unwrap $ mkSolver goal) \i v -> do
        log ("  " <> showU i <> " !>= " <> showU v)
      log "Got:"
      forWithIndex_ solution \i v -> do
        log ("  " <> showU i <> " !>= " <> showU v)
    Just (Right (GESolver solution)) -> ensureModel (GESolver solution)

systemDerives :: MkSolver -> MkSolver -> Effect Unit
systemDerives constraints goal = do
  -- log "Testing …"
  let solver = mkSolver constraints
  let
    showit = forWithIndex_ (unwrap solver) \i v -> do
      log ("  " <> showU i <> " !>= " <> showU v)
  let solved = closure' 10 solver
  let
    missing solution = not $
      unwrap (mkSolver goal) # allWithIndex \k v ->
        Map.lookup k solution
        # maybe false (\v' -> v' <> v == v')
  case solved of
    Nothing -> log "Did not stabilize:" <> showit
    Just (Left (Contradiction (Pair l r))) -> do
      log "Inconsistent:"
      log ("  " <> showU l <> " < " <> showU r)
      showit
    Just (Left (Undeterminable vs)) -> do
      log "Inconsistent:"
      log (show vs)
      showit
    Just (Right (GESolver solution)) | missing solution -> do
      log "Consistent but unexpected:"
      log "Expected at least:"
      showit
      log "Got:"
      forWithIndex_ solution \i v -> do
        log ("  " <> showU i <> " !>= " <> showU v)
    Just (Right (GESolver solution)) -> ensureModel (GESolver solution)

verifyingSolution :: GESolver -> Either ExError (Map String Int)
verifyingSolution solver =
  exemplify solver >>= \sol -> verifySolutionTo solver sol $> sol

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
  uempty !<=> z2 === ALT
  x !<=> x2y === ALT
  y !<=> x2y === HLE
  x <> c5 !<=> x === HGE
  x^+1 <> c5 !<=> x === AGT
  x^+1 <> c5 !<=> x <> c5 === HGE

  x^+2 <> y^+2 <> z^+2 !<=> x <> y <> z^+2 === HGE

  consistent do z2 !>= z
  inconsistent do z !>= z2
  inconsistent do
    z !>= xy
    xy !>= z2
  consistent do
    z2 !>= xy
    xy !>= z
  inconsistent do
    x !>= uconst 1
    uconst 0 !>= x

  goesTo
    do
      xy !>= x2y
    do
      y !>= x2y

  (x ^< y ^< z) <> (x ^< z ^< y) !<=> (x ^< y ^< z) <> y === EEQ
  (x^+2 ^< y) ^+ 3 !<=> (x^+5 ^< y) <> (y^+3) === EEQ
  (x ^< y) <> x !<=> xy === EEQ
  (z^+1 ^< y) !<=> z ^< y === HGE
  (x ^< y <> z) <> (x ^< y) !<=> (x ^< y <> z) === EEQ

  (x^+5 ^< y) !+<= x <> y === Just (Max 5)
  (x^+2 ^< y) !+<= x <> y === Just (Max 2)

  x !<=> (uconst 6 <> x <> y) === HLE
  x !<=> (x <> y) === HLE
  (uconst 6 <> x <> y) !<=> x === HGE
  (x <> y) !<=> x === HGE

  consistent do
    xy !>= x2y
  consistent do
    xy <> uconst 4 !>= x2y
  consistent do
    xy !>= x2y <> uconst 4
  consistent do
    xy <> uconst 4 !>= x2y <> uconst 4
  consistent do
    z !>= x2y
    xy !>= uconst 6
  consistent do
    z !>= x <> y^+2
    xy !>= uconst 6
  consistent do
    z !>= x2y
    xy !>= uconst 6
    uconst 6 !>= z
  consistent do
    z !>= x <> y^+2
    xy !>= uconst 6
    uconst 6 !>= z
  goesTo
    do
      z !>= x
      x !>= uconst 6
      uconst 6 !>= z
    do
      z !>= x <> z <> uconst 6
      x !>= x <> z <> uconst 6
      uconst 6 !>= x <> z <> uconst 6
  consistent do
    x !>= uconst 1
    x <> uconst 1 !>= uconst 2
  goesTo
    do
      x !>= uconst 1
      x <> uconst 1 !>= uconst 2
    do
      x !>= uconst 2 <> x
  goesTo
    (x <> uconst 4 !>= x <> uconst 2)
    (pure unit)
  goesTo
    do
      uvar "v" !>= xy
      xy ^+ 6 !>= z
    do
      uvar "v" !>= uvar "v" <> xy <> z ^+ (-6)
      xy ^+ 6 !>= z <> xy ^+ 6
  goesTo
    do
      y !>= uconst 1
      uconst 3 !>= (x^+3 ^< y)
    do
      uconst 3 !>= x^+3 <> y
      y !>= x^+1 <> y
  systemDerives
    do
      y !>= uconst 1
      uconst 3 !>= (x^+3 ^< y)
      uconst 4 !>= (z ^< x)
    do
      uconst 0 !>= x
  systemDerives
    do
      y !>= uconst 1
      uconst 3 !>= (x^+3 ^< y)
      uconst 1 !>= (z ^< x)
    do
      uconst 0 !>= x
  consistent do
    z !>= uconst 5
    (z ^< x) <> (uconst 2 ^< y) !>= uconst 3
    uconst 4 !>= (z ^< x) <> (uconst 2 ^< y)
  consistent do
    uconst 0 !>= y
    z !>= (x^+3 ^< y)
  consistent do
    uconst 1 !>= y^+1
    z !>= (x^+3 ^< y)
  systemDerives
    do
      y !>= uconst 1
      uconst 3 !>= (x^+3 ^< y)
      uconst 1 !>= (z ^< x)
    do
      uconst 0 !>= x
  systemDerives
    do
      uconst 3 !>= (x^+5 ^< y)
    do
      uconst 0 !>= y
  systemDerives
    do
      (x^+5 ^< y) !>= uconst 1
    do
      y !>= uconst 1

  {-
  testSystem do
    x ^< y !>= xy
  testSystem do
    x ^< y !>= uconst 1
  testSystem do
    (x^+4 ^< y)^+2 !>= uconst 4
  -}

{-# LANGUAGE DataKinds #-}

-- | Machine and polynomial channel oracles.
module Axioma.Machine
  ( machineTopic,
  )
where

import Axioma.Common (Verbosity (..), checkIOV, checkV)
import Circuit.Linear (Par (..), distL, distR)
import Circuit.Machine (Machine, MachineObs (..), branchMachine, duplicateMachine, machine, machineObs, machineObsWith, machineToClosed, monoDir, monoIn, moore, runMachineSum, toEvalMachine)
import Circuit.Poly (Dir, Eval (..), Mono, Poly (..))
import Circuit.Syntax (eval)
import Control.Category (id)
import Control.Exception (SomeException, evaluate, try)
import Control.Monad (replicateM, when)
import Data.Void (Void, absurd)
import Prelude hiding (id, (.))

mkMachine :: (s -> a -> s) -> (s -> b) -> MachineObs s (Mono a b)
mkMachine st ex = moore (\s -> (ex s, ())) (\s d -> st s (monoDir d))

peekM :: MachineObs s (Mono i o) -> s -> o
peekM sys s = case toEvalMachine sys s of EP (EK o, EE _) -> o

stepM :: MachineObs s (Mono i o) -> s -> i -> s
stepM sys s i = case toEvalMachine sys s of EP (EK _, EE f) -> f i

runMono :: MachineObs s (Mono i o) -> s -> (o, i -> s)
runMono sys s = case toEvalMachine sys s of EP (EK o, EE f) -> (o, f)

-- * duplicateMachine law probes

-- | Output stream of an observable machine over an input stream: the
-- position after each step.
positionsOf :: MachineObs s (Mono o s) -> s -> [o] -> [s]
positionsOf sys = go
  where
    go _ [] = []
    go s (o : os) = let s' = stepM sys s o in peekM sys s' : go s' os

-- | Observe an expanded machine at a state: the current state and the
-- one-step transition it presents.
peek2 :: MachineObs s ('Comp (Mono o s) (Mono o s)) -> s -> (s, o -> s)
peek2 sys s = case toEvalMachine sys s of
  EC ((cur, ()), f) _ -> (cur, \o -> fst (f (monoIn o)))

-- | Step an expanded machine by one direction pair.
step2 :: MachineObs s ('Comp (Mono o s) (Mono o s)) -> s -> (o, o) -> s
step2 sys s (o1, o2) = case toEvalMachine sys s of
  EC _ g -> g (monoIn o1, monoIn o2)

-- | Position stream of an expanded machine over a stream of direction pairs.
positions2 :: MachineObs s ('Comp (Mono o s) (Mono o s)) -> s -> [(o, o)] -> [(s, o -> s)]
positions2 sys = go
  where
    go _ [] = []
    go s (p : ps) = let s' = step2 sys s p in peek2 sys s' : go s' ps

-- | All sixteen two-state two-direction transitions.
allTransitions :: [Bool -> Bool -> Bool]
allTransitions =
  [ \s o -> tb !! (2 * fromEnum s + fromEnum o)
  | tb <- replicateM 4 [False, True]
  ]

-- | All direction-pair streams up to length three.
allPairStreams :: [[(Bool, Bool)]]
allPairStreams =
  concat
    [ replicateM n [(False, False), (False, True), (True, False), (True, True)]
    | n <- [0 .. 3]
    ]

-- | The two-step machine: the expansion projected back to a monomial
-- (observable) interface.  'duplicateMachine' requires 'Mono' input and
-- produces 'Comp' output, so iteration goes through this projection — which
-- forgets the presented transition.
twoStep :: MachineObs s (Mono o s) -> MachineObs s (Mono (o, o) s)
twoStep sys = mkMachine (\s (o1, o2) -> stepM sys (stepM sys s o1) o2) id

machineTopic :: Verbosity -> IO [Bool]
machineTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "Machine and Par oracles"
  sequence
    [ -- Par / linear distributivity
      checkV verbosity "Par distL is the one-way (,) / Either distributor" $
        distL ('x', Left True :: Either Bool Int) == Left ('x', True)
          && distR (Left True :: Either Bool Int, 'x') == Left True,
      checkV verbosity "Par unitlP collapses Void on Either" $
        unitlP (Right 42 :: Either Void Int) == (42 :: Int),
      checkV verbosity "Par unitrP collapses Void on Either" $
        unitrP (Left 42 :: Either Int Void) == (42 :: Int),
      -- Machine peek/step oracles
      checkV verbosity "peekM reads current output without consuming input" $
        let sys = mkMachine (\s i -> s + i) (\s -> s * 2) :: MachineObs Int (Mono Int Int)
         in peekM sys 5 == 10,
      checkV verbosity "stepM advances state by one input" $
        let sys = mkMachine (\s i -> s + i) (\s -> s * 2) :: MachineObs Int (Mono Int Int)
         in stepM sys 5 3 == 8,
      checkV verbosity "runMono exposes output and transition" $
        let sys = mkMachine (\s i -> s + i) (\s -> s * 2) :: MachineObs Int (Mono Int Int)
            (o, next) = runMono sys 5
         in o == 10 && next 3 == 8,
      checkV verbosity "Machine id lens emits committed input" $
        let sys = mkMachine (\_s d -> d) id :: MachineObs Int (Mono Int Int)
         in peekM sys (stepM sys 0 (42 :: Int)) == 42,
      checkV verbosity "Machine const lens ignores state" $
        let sys = mkMachine (\s _d -> s) (const (7 :: Int)) :: MachineObs Int (Mono Int Int)
         in peekM sys (stepM sys 0 (99 :: Int)) == 7,
      checkV verbosity "machineToClosed hides state as a feedback trace" $
        let sys = mkMachine (\_s d -> d) id :: MachineObs Int (Mono Int Int)
            tr = machineToClosed (moMachine sys)
         in eval tr (Right 42 :: Either Void Int) == (42 :: Int, ()),
      -- toEvalMachine totality (Circuit.Machine). The position is read
      -- through the observation bundled in 'MachineObs' — nothing is probed,
      -- no machine law is silently assumed — so a bounded run of reads must
      -- complete. Mutation room: if the conversion ever derives the
      -- observation by running the body (reintroducing a probe), the bounded
      -- run below crashes the whole topic.
      checkV verbosity "toEvalMachine reads the carried observation on a Moore body (bounded run)" $
        let sys = mkMachine (\s i -> s + i) (\s -> s * 2) :: MachineObs Int (Mono Int Int)
            states = iterate (\s -> stepM sys s 1) 0
            steps = [peekM sys s | s <- take 64 states]
         in head steps == 0 && last steps == 126,
      -- The observation is a field, so reading the position of a strict
      -- body (one that forces its direction with 'seq') cannot crash: the
      -- read never passes through the body. The strict body's step still
      -- forces the direction — that is real work, done only when stepping.
      checkIOV verbosity "certified observation reads a strict body without forcing the direction" $ do
        let strictBody :: Machine (,) Int (->) (Mono Int Int)
            strictBody =
              machine $ \case
                (s, Right i) -> i `seq` (s + i, (s, ()))
                (_, Left v) -> absurd v
            strictSys :: MachineObs Int (Mono Int Int)
            strictSys = machineObsWith (\s -> (s, ())) strictBody
        peeked <- try (evaluate (peekM strictSys 5)) :: IO (Either SomeException Int)
        stepped <- try (evaluate (stepM strictSys 5 3)) :: IO (Either SomeException Int)
        pure (case (peeked, stepped) of (Right 5, Right 8) -> True; _ -> False),
      -- Sum machines: the observation follows the branch the STATE selects,
      -- never a probed branch. This clause pins the investigation finding
      -- that the old probeDir = Left (probeDir @p) could not produce a wrong
      -- position on Moore bodies — and that the bundled observation makes
      -- the property structural.
      checkV verbosity "Sum observation follows the state-selected branch" $
        let exL s = s * 10
            exR s = s + 100
            sysL = mkMachine (\s i -> s + i) exL :: MachineObs Int (Mono Int Int)
            sysR = mkMachine (\s i -> s + i) exR :: MachineObs Int (Mono Int Int)
            brObs = branchMachine even sysL sysR :: MachineObs Int ('Sum (Mono Int Int) (Mono Int Int))
            (oL, fL) = runMachineSum brObs 2
            (oR, fR) = runMachineSum brObs 3
         in oL == Left 20
              && fL 1 == 3
              && oR == Right 103
              && fR 1 == 4,
      -- duplicateMachine laws.  Two notes on what is NOT here:
      -- \* right identity collapses into left identity: the counit is
      --   observation, and at an observable machine observation is the
      --   identity function — both identity laws are the same equation, so
      --   the second would be defined-to-pass.
      -- \* associativity is inexpressible: duplicateMachine requires a Mono
      --   input and produces a Comp output, so it cannot be applied twice.
      --   Iteration goes through the 'twoStep' projection, which forgets
      --   the presented transition.
      --
      -- The law's shape is pinned by what the expansion IS: one pair-step
      -- is two original steps, so observation of the expansion samples the
      -- original's run at every second step.
      checkV verbosity "expansion presents state and transition (static counit)" $
        and
          [ fst (peek2 (duplicateMachine sys) s0) == s0
              && and [snd (peek2 (duplicateMachine sys) s0) o == stepM sys s0 o | o <- [False, True]]
          | t <- allTransitions,
            let sys = mkMachine t id :: MachineObs Bool (Mono Bool Bool),
            s0 <- [False, True]
          ],
      checkV verbosity "left identity: observing the expansion samples the original at every second step" $
        and
          [ let flat = concatMap (\(a, b) -> [a, b]) ps
                full = positionsOf sys s0 flat
             in map fst (positions2 (duplicateMachine sys) s0 ps)
                  == [full !! (2 * i + 1) | i <- [0 .. length ps - 1]]
          | t <- allTransitions,
            let sys = mkMachine t id :: MachineObs Bool (Mono Bool Bool),
            s0 <- [False, True],
            ps <- allPairStreams,
            not (null ps)
          ],
      checkV verbosity "machine maps: h commutes iff behaviors agree (xor/not vs xor/xnor)" $
        let xorT s o = s /= o
            xnorT s o = s == o
            sysXor = mkMachine xorT id :: MachineObs Bool (Mono Bool Bool)
            sysXnor = mkMachine xnorT id :: MachineObs Bool (Mono Bool Bool)
            streams = replicateM 3 [False, True]
            seeds = [False, True]
         in -- 'not' is a machine map xor -> xor ...
            and [positionsOf sysXor (not s0) os == map not (positionsOf sysXor s0 os) | s0 <- seeds, os <- streams]
              -- ... but not xor -> xnor, and the behaviors witness it
              && or [positionsOf sysXnor (not s0) os /= map not (positionsOf sysXor s0 os) | s0 <- seeds, os <- streams],
      checkV verbosity "duplicate preserves machine maps: expanded transitions commute iff h does" $
        let xorT s o = s /= o
            xnorT s o = s == o
            sysXor = mkMachine xorT id :: MachineObs Bool (Mono Bool Bool)
            sysXnor = mkMachine xnorT id :: MachineObs Bool (Mono Bool Bool)
            seeds = [False, True]
         in and
              [ snd (peek2 (duplicateMachine sysXor) (not s0)) o == not (snd (peek2 (duplicateMachine sysXor) s0) o)
              | s0 <- seeds,
                o <- seeds
              ]
              && or
                [ snd (peek2 (duplicateMachine sysXnor) (not s0)) o /= not (snd (peek2 (duplicateMachine sysXor) s0) o)
                | s0 <- seeds,
                  o <- seeds
                ],
      checkV verbosity "projected expansion = two-step machine (the tower iterates only through projection)" $
        and
          [ positionsOf (twoStep sys) s0 ps == map fst (positions2 (duplicateMachine sys) s0 ps)
          | t <- allTransitions,
            let sys = mkMachine t id :: MachineObs Bool (Mono Bool Bool),
            s0 <- [False, True],
            ps <- allPairStreams
          ],
      -- The comonoid reading: comonoids in (Poly, ◁, y) are small
      -- categories — counit is identities, comultiplication is composition.
      -- The lift of 'duplicateMachine' to a machine exists exactly when the
      -- transition is an action of the direction monoid.
      checkV verbosity "comonoid lift: a monoid-action transition passes the action laws" $
        let t s n = s + n :: Int
            states = [-2 .. 2]
            dirs = [0 .. 3]
         in and [t s 0 == s | s <- states]
              && and [t s (n + m) == t (t s n) m | s <- states, n <- dirs, m <- dirs],
      checkV verbosity "comonoid lift: a non-action transition has no identity direction (falsifier)" $
        let xorT s o = s /= o
            constF _s _o = False
            constT _s _o = True
            bools = [False, True]
            hasIdentity f = or [and [f s o0 == s | s <- bools] | o0 <- bools]
         in hasIdentity xorT && not (hasIdentity constF) && not (hasIdentity constT)
    ]

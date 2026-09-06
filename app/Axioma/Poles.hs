{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

-- | Poles, Additive Poles, Stamped, Boundary, and markProcess oracles.
module Axioma.Poles
  ( polesTopic,
  )
where

import Axioma.Common (Verbosity (..), checkIOV, checkV)
import Circuit.Body (Body (..))
import Circuit.Category (K (..), id, runK, (.), (.>))
import Circuit.Container (SomePos (..), posAt, posOf)
import Circuit.Equip
  ( Boundary (..),
    Poles (..),
    Stamped (..),
    box,
    close,
    companionTight,
    compose,
    compose0,
    conjointTight,
    copycat,
    iomap,
    isMark,
    isPayload,
    open,
    plug,
    polesK,
    splay0,
  )
import Circuit.Equip qualified as Poles
import Circuit.Machine (Machine, MachineObs (..), branchMachine, machine, machineMorphism, machineObsWith, machineToPolesAt)
import Circuit.Poly (Dir, Mono, Poly (..))
import Circuit.Process (Moore (..), Process (..), asMoore, fold, markMoore, markProcess, scan, scanProcess)
import Circuit.Tensor (Bias (..))
import Control.Exception (SomeException, evaluate, try)
import Control.Monad (void, when)
import Data.IORef (modifyIORef', newIORef, readIORef, writeIORef)
import Data.Maybe (fromMaybe, isNothing)
import Data.Void (absurd)
import Prelude hiding (curry, id, uncurry, (.))

polesTopic :: Verbosity -> IO [Bool]
polesTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "Poles, Stamped, Boundary, and markProcess oracles"
  sequence
    [ -- Poles oracles
      checkV verbosity "box recovers the composed morphism on a unit pole" $
        let e :: Poles () (->) Int Int
            e = Poles (const ()) (const 42)
         in box e 0 == 42 && box e 7 == 42,
      checkV verbosity "close is not identity for a non-copycat pole" $
        let e :: Poles () (->) Int Int
            e = Poles (const ()) (const 42)
         in close e 0 == 42 && close e 7 == 42,
      checkIOV verbosity "residual observed: sequential boxes agree but residual is exposed" $ do
        ref <- newIORef (0 :: Int)
        let e1 :: Poles () (K IO) Int Int
            e1 = polesK (\x -> modifyIORef' ref (+ x)) (pure 0)
            e2 :: Poles () (K IO) Int Int
            e2 = polesK (\_ -> pure ()) (pure 1)
        r1 <- runK (box (Poles.compose0 e1 e2)) 5
        residual1 <- readIORef ref
        writeIORef ref 0
        r2 <- runK (box e2 . box e1) 5
        residual2 <- readIORef ref
        pure (r1 == r2 && r1 == 1 && residual1 == 5 && residual2 == 5),
      checkV verbosity "non-identity pole at Bool is not the copycat" $
        let e :: Poles Bool (->) Int Int
            e = Poles (const False) (const 0)
         in close e 42 == 0,
      checkV verbosity "copycat is the identity at any carrier, including Bool" $
        let e :: Poles Bool (->) Bool Bool
            e = copycat
         in close e True && not (close e False),
      -- Additive Poles oracles
      checkV verbosity "Additive Poles.pair pairs outputs" $
        let e1 :: Poles () (->) () Int
            e1 = Poles (const ()) (const 1)
            e2 :: Poles () (->) () Int
            e2 = Poles (const ()) (const 2)
         in close (Poles.pair e1 e2) () == (1, 2),
      checkV verbosity "Poles.race LeftFirst picks left when both speak" $
        let eL :: Poles () (->) () (Maybe Int)
            eL = Poles (const ()) (const (Just 1))
            eR :: Poles () (->) () (Maybe Int)
            eR = Poles (const ()) (const (Just 2))
         in close (Poles.race isNothing LeftFirst eL eR) () == Just 1,
      checkV verbosity "Poles.race RightFirst picks right when both speak" $
        let eL :: Poles () (->) () (Maybe Int)
            eL = Poles (const ()) (const (Just 1))
            eR :: Poles () (->) () (Maybe Int)
            eR = Poles (const ()) (const (Just 2))
         in close (Poles.race isNothing RightFirst eL eR) () == Just 2,
      checkV verbosity "Poles.race falls back when left is silent" $
        let eL :: Poles () (->) () (Maybe Int)
            eL = Poles (const ()) (const Nothing)
            eR :: Poles () (->) () (Maybe Int)
            eR = Poles (const ()) (const (Just 2))
         in close (Poles.race isNothing LeftFirst eL eR) () == Just 2
              && close (Poles.race isNothing RightFirst eL eR) () == Just 2,
      -- Polynomial structured-channel oracles (equip-next phase 6) retired
      -- with the Chs flat grade: the "flat channel ignores its carrier"
      -- finding is captured at commit 0b1663e and on loom/poly-containers.
      -- Honest-grade oracles (poly-containers phase C): the carrier is a
      -- SomePos position, so no observation argument is needed.
      checkV verbosity "machineToPolesAt write leg posts posAt of the stepped position" $
        let stepInc (s, d) = case d of
              Left v -> absurd v
              Right i -> (s + i, (s, ()))
            stepDbl (s, d) = case d of
              Left v -> absurd v
              Right i -> (s + i, (s * 2, ()))
            inc = machineObsWith (\s -> (s, ())) (machine stepInc) :: MachineObs Int (Mono Int Int)
            dbl = machineObsWith (\s -> (s * 2, ())) (machine stepDbl) :: MachineObs Int (Mono Int Int)
            sys = moMachine (branchMachine odd inc dbl) :: Machine (,) Int (->) ('Sum (Mono Int Int) (Mono Int Int))
            p = machineToPolesAt sys
            inputs = [Left (Right 1), Right (Right 1), Left (Right 1)] :: [Dir ('Sum (Mono Int Int) (Mono Int Int))]
            posOfSome (SomePos i) = posOf i
            run _ [] acc = acc
            run s (d : ds) acc =
              let (s', pos) = machineMorphism sys (s, d)
                  (s'', ch) = morphism (conjoint p) (s, d)
               in run s' ds (acc && s'' == s' && posOfSome ch == pos)
         in run 1 inputs True,
      checkV verbosity "the position carrier feeds the read leg: honest poles distinguish the branches" $
        let stepInc (s, d) = case d of
              Left v -> absurd v
              Right i -> (s + i, (s, ()))
            stepDbl (s, d) = case d of
              Left v -> absurd v
              Right i -> (s + i, (s * 2, ()))
            inc = machineObsWith (\s -> (s, ())) (machine stepInc) :: MachineObs Int (Mono Int Int)
            dbl = machineObsWith (\s -> (s * 2, ())) (machine stepDbl) :: MachineObs Int (Mono Int Int)
            sys = moMachine (branchMachine odd inc dbl) :: Machine (,) Int (->) ('Sum (Mono Int Int) (Mono Int Int))
            p = machineToPolesAt sys
            r = companion p
            leftCar = posAt @('Sum (Mono Int Int) (Mono Int Int)) (Left (4, ()))
            rightCar = posAt @('Sum (Mono Int Int) (Mono Int Int)) (Right (4, ()))
         in morphism r (4, leftCar) /= morphism r (4, rightCar)
              && morphism r (3, leftCar) /= morphism r (3, rightCar),
      checkV verbosity "position recovery: the carrier alone determines the read" $
        let stepInc (s, d) = case d of
              Left v -> absurd v
              Right i -> (s + i, (s, ()))
            stepDbl (s, d) = case d of
              Left v -> absurd v
              Right i -> (s + i, (s * 2, ()))
            inc = machineObsWith (\s -> (s, ())) (machine stepInc) :: MachineObs Int (Mono Int Int)
            dbl = machineObsWith (\s -> (s * 2, ())) (machine stepDbl) :: MachineObs Int (Mono Int Int)
            sys = moMachine (branchMachine odd inc dbl) :: Machine (,) Int (->) ('Sum (Mono Int Int) (Mono Int Int))
            p = machineToPolesAt sys
            inputs = [Left (Right 1), Right (Right 1), Left (Right 1)] :: [Dir ('Sum (Mono Int Int) (Mono Int Int))]
            posOfSome (SomePos i) = posOf i
            collect _ [] acc = acc
            collect s (d : ds) acc =
              let (s', _) = machineMorphism sys (s, d)
                  (_, ch) = morphism (conjoint p) (s, d)
               in collect s' ds (ch : acc)
            check [] acc = acc
            check (ch : chs) acc =
              let (_, posA) = morphism (companion p) (0, ch)
                  (_, posB) = morphism (companion p) (99, ch)
               in check chs (acc && posA == posOfSome ch && posB == posA)
         in check (reverse (collect 1 inputs [])) True,
      -- Stamped oracles
      checkV verbosity "Stamped fmap preserves stamp (Int token)" $
        let s = Stamped 7 ("hello" :: String)
         in stamp (fmap reverse s) == (7 :: Int) && stamped (fmap reverse s) == "olleh",
      checkV verbosity "Stamped fmap preserves stamp (Bool token)" $
        let s = Stamped True (10 :: Int)
         in stamp (fmap (+ 1) s) && stamped (fmap (+ 1) s) == 11,
      -- Boundary oracles
      checkV verbosity "Boundary fmap preserves Mark tag" $
        isMark (fmap length (Mark "halt" :: Boundary String String)),
      checkV verbosity "Boundary fmap acts on Payload" $
        let p = fmap length (Payload "hi" :: Boundary String String)
         in isPayload p && p == Payload 2,
      -- Mark system (circuits-residual §7)
      checkV verbosity "markProcess steps payloads through the inner system" $
        let innerP = Process 0 (+) id :: Process Int Int Int
            sys = markProcess (== "HALT") innerP
            p = asMoore sys
         in scan p (map Payload [1, 2, 3]) == [Just 1, Just 3, Just 6],
      checkV verbosity "markProcess halts on a halt mark and emits Nothing thereafter" $
        let innerP = Process 0 (+) id :: Process Int Int Int
            sys = markProcess (== "HALT") innerP
            p = asMoore sys
         in scan p [Payload 1, Payload 2, Mark "HALT", Payload 3] == [Just 1, Just 3, Nothing, Nothing],
      checkV verbosity "markProcess treats non-halt marks as no-ops" $
        let innerP = Process 0 (+) id :: Process Int Int Int
            sys = markProcess (== "HALT") innerP
            p = asMoore sys
         in scan p [Payload 1, Mark "NOOP", Payload 2] == [Just 1, Just 1, Just 3],
      checkV verbosity "markProcess halts immediately when the first input is a halt mark" $
        let innerP = Process 0 (+) id :: Process Int Int Int
            sys = markProcess (== "HALT") innerP
            p = asMoore sys
         in scan p [Mark "HALT", Payload 1] == [Nothing, Nothing],
      checkV verbosity "markProcess round-trips through Moore" $
        let innerP = Process 0 (+) id :: Process Int Int Int
            sys = markProcess (== "HALT") innerP
            p = asMoore sys
         in null (scan p []) && fold p [Payload 1, Payload 2, Mark "HALT"] == Just Nothing,
      -- The documented asymmetry (Process.hs:251): the unpointed
      -- 'markMoore' has no seed, so an initial mark without payload reaches
      -- 'error "markMoore: initial mark without payload"' — a runtime
      -- error, not a silent default. 'markProcess' exists precisely to
      -- remove that: its seed is already live, so a non-halt mark is a no-op
      -- from the very first input. Mutation room: delete the error branch in
      -- 'markMoore' (mapping the initial mark to a made-up state) and the
      -- first oracle silently passes while the asymmetry is gone.
      checkIOV verbosity "markMoore errors on an initial mark without payload" $ do
        let inner = Moore id (+) id :: Moore Int Int
            p = markMoore (== "HALT") inner
        result <- try (evaluate (fromMaybe 0 (head (scan p [Mark "NOOP"])))) :: IO (Either SomeException Int)
        pure (case result of Left _ -> True; Right _ -> False),
      checkV verbosity "markProcess seeds past the initial-mark asymmetry" $
        let innerP = Process 0 (+) id :: Process Int Int Int
            sys = markProcess (== "HALT") innerP
         in scanProcess sys [Mark "NOOP", Payload 1, Mark "HALT", Payload 2]
              == [Just 0, Just 1, Nothing, Nothing],
      -- equipment-law oracles
      checkV verbosity "close is a homomorphism for stateful Poles over Body" $
        let w1 = Body (\(s, x) -> let s' = s + x in (s', s')) :: Body (,) Int (->) Int Int
            r1 = Body (\(s, ch) -> (s, ch)) :: Body (,) Int (->) Int Int
            p1 = Poles w1 r1 :: Poles Int (Body (,) Int (->)) Int Int
            w2 = Body (\(s, x) -> let s' = s * x in (s', s')) :: Body (,) Int (->) Int Int
            r2 = Body (\(s, ch) -> (s, ch + 1)) :: Body (,) Int (->) Int Int
            p2 = Poles w2 r2 :: Poles Int (Body (,) Int (->)) Int Int
            lhs = close (compose p1 p2) :: Body (,) Int (->) Int Int
            rhs = close p1 .> close p2
         in morphism lhs (2, 3) == morphism rhs (2, 3)
              && morphism lhs (1, 4) == morphism rhs (1, 4),
      checkV verbosity "open is the identity for Poles composition at unit" $
        let p = Poles (const ()) (const 42 :: () -> Int) :: Poles () (->) () Int
            o = open :: Poles () (->) () ()
            pL = compose0 o p
            (w, r) = splay0 p
            (wL, rL) = splay0 pL
         in wL () == w () && rL () == r () && box (compose0 o p) () == box p (),
      checkV verbosity "Body (,) unit poles yank to identity" $
        let b = close (open :: Poles () (Body (,) Int (->)) () ()) :: Body (,) Int (->) () ()
         in morphism b (42, ()) == (42, ()) && morphism b (0, ()) == (0, ()),
      checkV verbosity "Body Either unit poles yank to identity" $
        let b = close (open :: Poles () (Body Either [Int] (->)) () ()) :: Body Either [Int] (->) () ()
         in morphism b (Left [1, 2, 3]) == Left [1, 2, 3],
      -- Tight-arrow companion / conjoint oracles
      checkV verbosity "companionTight posts a unit-incident arrow as the read leg" $
        let f = const 42 :: () -> Int
            o = companionTight f :: Poles () (->) () Int
         in box o () == 42,
      checkV verbosity "conjointTight pres a unit-incident arrow as the write leg" $
        let f = const () :: Int -> ()
            i = conjointTight f :: Poles () (->) Int ()
         in box i 7 == (),
      checkV verbosity "compose of conjointTight and companionTight recovers composition" $
        let f = const () :: Int -> ()
            g = const 42 :: () -> Int
         in close (compose (conjointTight f) (companionTight g)) 7 == 42,
      checkV verbosity "composed tight poles agree with f .> g" $
        let f = const () :: Int -> ()
            g = const 42 :: () -> Int
         in close (compose (conjointTight f) (companionTight g)) 5 == (g . f) 5,
      -- Spiwak restriction stability on an effectful base:
      -- R(f.h, g.j) = R(f,g)(h,j) as iomap fusion.  On K IO the content is
      -- effect sequencing: both sides must return equal results with equal
      -- log order (the whiskers transform the payload, so they log before
      -- the base legs).  The swapped-whisker run pins the probe as
      -- order-sensitive, so a passing fusion check is known non-vacuous.
      -- Mutation room: an associativity violation in iomap or (.>) shows
      -- up as log order divergence ("f","h","w",... against "h","f","w",...).
      checkIOV verbosity "iomap fusion on K IO: equal results and equal effect order" $ do
        ref <- newIORef ([] :: [String])
        let logTag :: String -> IO ()
            logTag tag = modifyIORef' ref (++ [tag])
            p0 :: Poles () (K IO) Int Int
            p0 =
              Poles
                (K (\_ -> void (logTag "w")))
                (K (\_ -> logTag "r" >> pure 7))
            f, h, g, j :: K IO Int Int
            f = K (\x -> logTag "f" >> pure (x + 1))
            h = K (\x -> logTag "h" >> pure (x * 2))
            g = K (\x -> logTag "g" >> pure (x + 1))
            j = K (\x -> logTag "j" >> pure (x * 10))
            lhs = iomap h j (iomap f g p0)
            rhs = iomap (h .> f) (g .> j) p0
            swapped = iomap (f .> h) (j .> g) p0
        r1 <- runK (box lhs) 5
        log1 <- readIORef ref
        writeIORef ref []
        r2 <- runK (box rhs) 5
        log2 <- readIORef ref
        writeIORef ref []
        _ <- runK (box swapped) 5
        log3 <- readIORef ref
        pure
          ( r1 == r2
              && log1 == log2
              && log1 == ["h", "f", "w", "r", "g", "j"]
              && log3 == ["f", "h", "w", "r", "j", "g"]
          )
    ]

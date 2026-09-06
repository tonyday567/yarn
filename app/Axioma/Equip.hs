-- | Arrow-equipment oracles: squares, feedback-category laws, and carriers.
module Axioma.Equip
  ( equipTopic,
  )
where

import Axioma.Bisim (bisimilarStates, isBisimulation, maxBisimulation)
import Axioma.Common (Verbosity (..), checkV)
import Circuit.Body (Body (..), runFlowchart, seqCompose)
import Circuit.Category ((.>))
import Circuit.Category qualified as Cat
import Circuit.Equip
  ( Poles (..),
    Sq (..),
    acrossThenDown,
    associatorSq,
    checkSq,
    close,
    downThenAcross,
    hcompose,
    idSq,
    iomap,
    leftWhisker,
    rightWhisker,
    unitorLeftSq,
    unitorRightSq,
    vcomp,
    whiskerSq,
  )
import Circuit.Process (bodyToMoore, scan)
import Circuit.Tensor (Action (..), Distributive (..), Tensor (..), Unital (..))
import Circuit.Traced (Assoc (..), Slide (..), Strength (..))
import Control.Monad (when)
import Data.Bifunctor (first)
import Data.List (sort)
import Data.Maybe (isNothing)
import Data.These (These (..))
import Data.Void (Void, absurd)

-- | Exact-oracle range for the two-cell checks.
carrierRange :: [Int]
carrierRange = [-16 .. 16]

-- | Smaller range for associator and strength-coherence oracles, where the
-- state space is a product.
smallRange :: [Int]
smallRange = [-2 .. 2]

-- | Counter with reset: state is an 'Int', payload is a reset flag.
--
-- Output is a 'Char' marking the parity of the /new/ state.
counterBody :: Body (,) Int (->) Bool Char
counterBody = Body $ \(n, r) -> let n' = if r then 0 else n + 1 in (n', if odd n' then 'x' else 'y')

-- | Boolean flip with reset: state is a 'Bool', payload is a reset flag.
--
-- Output is a 'Char' marking the new state.
parityBody :: Body (,) Bool (->) Bool Char
parityBody = Body $ \(b, r) -> let b' = not r && not b in (b', if b' then 'x' else 'y')

-- | Carrier map: counter parity agrees with boolean state.
counterToParitySq :: Sq (,) (->) Int Bool Bool Char
counterToParitySq = Sq odd counterBody parityBody

-- | One-token mutation: observe even-ness instead of odd-ness.
brokenBody :: Body (,) Int (->) Bool Char
brokenBody = Body $ \(n, r) -> let n' = if r then 0 else n + 1 in (n', if even n' then 'x' else 'y')

brokenSq :: Sq (,) (->) Int Bool Bool Char
brokenSq = Sq odd brokenBody parityBody

-- | One-token mutation: reset lands on 1 instead of 0.  The observation is
-- internally consistent; only the state transport through @odd@ breaks.
resetDriftBody :: Body (,) Int (->) Bool Char
resetDriftBody = Body $ \(n, r) -> let n' = if r then 1 else n + 1 in (n', if odd n' then 'x' else 'y')

resetDriftSq :: Sq (,) (->) Int Bool Bool Char
resetDriftSq = Sq odd resetDriftBody parityBody

-- | Reference implementation of carrier-tensoring composition, kept as an
-- independent specification against which 'seqCompose' is checked.
_seqComposeReference ::
  Body (,) s2 (->) b c ->
  Body (,) s1 (->) a b ->
  Body (,) (s1, s2) (->) a c
_seqComposeReference (Body g) (Body f) =
  Body $ \((s1', s2'), a) ->
    let (s1'', b) = f (s1', a)
        (s2'', c) = g (s2', b)
     in ((s1'', s2''), c)

-- | Bodies for the observational cascade tests.  They are intentionally
-- non-commuting and time-varying so that composition order is observable.
sumBody :: Body (,) Int (->) Int Int
sumBody = Body $ \(s, a) -> (s + a, s + a)

maxBody :: Body (,) Int (->) Int Int
maxBody = Body $ \(s, a) -> let s' = max s a in (s', s')

delayBody :: Body (,) Int (->) Int Int
delayBody = Body $ \(s, a) -> (a, s)

-- | Stream-composition oracle: 'seqCompose' agrees with running two bodies
-- in sequence on the input list.  @sumBody@ and @maxBody@ do not commute, so a
-- reversed composition order is caught.
--
-- Distinct seeds (0 and -5) ensure a wrongly-paired seed tuple is visible.
cascadeStreamOk :: [Int] -> Bool
cascadeStreamOk xs =
  let s1 = 0
      s2 = -5
   in scan (bodyToMoore (seqCompose maxBody sumBody) (s1, s2)) xs
        == scan (bodyToMoore maxBody s2) (scan (bodyToMoore sumBody s1) xs)

-- | Associativity oracle: 'seqCompose' is associative on input lists.  All
-- three bodies are input- and state-sensitive; @doublerBody@ was removed
-- because it discarded its input and made the test vacuous.
--
-- Distinct seeds (7, 0, -5) catch seed mis-pairing.
cascadeAssocOk :: [Int] -> Bool
cascadeAssocOk xs =
  let f = delayBody
      g = sumBody
      h = maxBody
      s1 = 7
      s2 = 0
      s3 = -5
   in scan (bodyToMoore (seqCompose h (seqCompose g f)) ((s1, s2), s3)) xs
        == scan (bodyToMoore (seqCompose (seqCompose h g) f) (s1, (s2, s3))) xs

-- | 'seqCompose' agrees with the independent reference implementation.
-- Distinct seeds catch seed mis-pairing.
seqComposeAgreesOk :: [Int] -> Bool
seqComposeAgreesOk xs =
  let s1 = 2
      s2 = -3
   in scan (bodyToMoore (seqCompose maxBody sumBody) (s1, s2)) xs
        == scan (bodyToMoore (_seqComposeReference maxBody sumBody) (s1, s2)) xs

-- | Left identity for carrier-tensoring composition.
seqComposeLeftIdOk :: [Int] -> Bool
seqComposeLeftIdOk xs =
  let s = 7
   in scan (bodyToMoore (seqCompose sumBody (Body id)) ((), s)) xs == scan (bodyToMoore sumBody s) xs

-- | Right identity for carrier-tensoring composition.
seqComposeRightIdOk :: [Int] -> Bool
seqComposeRightIdOk xs =
  let s = 7
   in scan (bodyToMoore (seqCompose (Body id) sumBody) (s, ())) xs == scan (bodyToMoore sumBody s) xs

-- | Machine-split 'Poles' for the counter body.  The write pole updates state
-- and posts the new state into the carrier; the read pole observes the carrier
-- and emits a 'Char'.
counterPoles :: Poles Int (Body (,) Int (->)) Bool Char
counterPoles = Poles write readBody
  where
    write = Body $ \(n, r) -> let n' = if r then 0 else n + 1 in (n', n')
    readBody = Body $ \(n, ch) -> (n, if odd ch then 'x' else 'y')

-- | Machine-split 'Poles' for the parity body.
parityPoles :: Poles Bool (Body (,) Bool (->)) Bool Char
parityPoles = Poles write readBody
  where
    write = Body $ \(b, r) -> let b' = not r && not b in (b', b')
    readBody = Body $ \(b, ch) -> (b, if ch then 'x' else 'y')

-- | Plain boundary maps for the interchange test.  They are type-changing so
-- that swapping them is a type error and applying them twice is not an
-- involution.
boundaryF :: Int -> Bool
boundaryF = odd

boundaryG :: Char -> String
boundaryG c = [c, c]

-- | 'boundaryF' lifted to a 'Body' morphism.  State is threaded through
-- unchanged; only the payload is mapped.
bodyF :: Body (,) s (->) Int Bool
bodyF = Body $ \(s, a) -> (s, boundaryF a)

-- | 'boundaryG' lifted to a 'Body' morphism.
bodyG :: Body (,) s (->) Char String
bodyG = Body $ \(s, c) -> (s, boundaryG c)

-- | The Machine-split 'Poles' representations agree with the original Moore
-- bodies over the full bounded state space.
polesMatchBodyOk :: Bool
polesMatchBodyOk =
  all
    (\(n, r) -> morphism (close counterPoles) (n, r) == morphism counterBody (n, r))
    [(n, r) | n <- carrierRange, r <- [False, True]]
    && all
      (\(b, r) -> morphism (close parityPoles) (b, r) == morphism parityBody (b, r))
      [(b, r) | b <- [False, True], r <- [False, True]]

-- | Interchange law, source side: boundary whisker on 'Sq' equals 'iomap' on
-- the 'Poles' representation.
interchangeSourceOk :: (Int, Int) -> Bool
interchangeSourceOk (n, r) =
  let polesSide = close (iomap bodyF bodyG counterPoles)
      bodySide = sqSrc (whiskerSq boundaryF boundaryG counterToParitySq)
   in morphism polesSide (n, r) == morphism bodySide (n, r)

-- | Interchange law, target side.
interchangeTargetOk :: (Bool, Int) -> Bool
interchangeTargetOk (b, r) =
  let polesSide = close (iomap bodyF bodyG parityPoles)
      bodySide = sqTgt (whiskerSq boundaryF boundaryG counterToParitySq)
   in morphism polesSide (b, r) == morphism bodySide (b, r)

-- | Bodies for the horizontal 2-cell tests.  Each machine's output depends on
-- its carrier, so dropped state threads are visible.
echoBody :: Body (,) Int (->) Char Char
echoBody = Body $ \(n, x) -> (n + 1, if odd n then x else 'z')

echoParityBody :: Body (,) Bool (->) Char Char
echoParityBody = Body $ \(b, x) -> (not b, if b then x else 'z')

echoSq :: Sq (,) (->) Int Bool Char Char
echoSq = Sq odd echoBody echoParityBody

rightWhiskerBody :: Body (,) Int (->) Char Int
rightWhiskerBody = Body $ \(s, x) -> (s + 1, if x == 'x' then s else negate s)

leftWhiskerBody :: Body (,) Int (->) Int Bool
leftWhiskerBody = Body $ \(s, a) -> (s + a, odd s)

-- | Observational right-whisker oracle: running the whiskered source/target
-- bodies must equal running the corresponding square bodies followed by the
-- whisker body.  Distinct seeds catch seed mis-pairing.
rightWhiskerObservationalOk :: [Bool] -> Bool
rightWhiskerObservationalOk rs =
  let sq = rightWhisker counterToParitySq rightWhiskerBody
      counterOuts = scan (bodyToMoore counterBody 3) rs
      hOutsSrc = scan (bodyToMoore rightWhiskerBody (-2)) counterOuts
      sqOutsSrc = scan (bodyToMoore (sqSrc sq) (3, -2)) rs
      parityOuts = scan (bodyToMoore parityBody False) rs
      hOutsTgt = scan (bodyToMoore rightWhiskerBody (-2)) parityOuts
      sqOutsTgt = scan (bodyToMoore (sqTgt sq) (False, -2)) rs
   in sqOutsSrc == hOutsSrc && sqOutsTgt == hOutsTgt

-- | Square-preservation check: right whisker yields a commuting square.
rightWhiskerSquareOk :: Bool
rightWhiskerSquareOk =
  let sq = rightWhisker counterToParitySq rightWhiskerBody
   in all
        (\((n, s), r) -> downThenAcross sq ((n, s), r) == acrossThenDown sq ((n, s), r))
        [((n, s), r) | n <- carrierRange, s <- carrierRange, r <- [False, True]]

-- | Observational left-whisker oracle.
leftWhiskerObservationalOk :: [Int] -> Bool
leftWhiskerObservationalOk xs =
  let sq = leftWhisker leftWhiskerBody counterToParitySq
      lOutsSrc = scan (bodyToMoore leftWhiskerBody 1) xs
      counterOuts = scan (bodyToMoore counterBody 4) lOutsSrc
      sqOutsSrc = scan (bodyToMoore (sqSrc sq) (1, 4)) xs
      lOutsTgt = scan (bodyToMoore leftWhiskerBody 1) xs
      parityOuts = scan (bodyToMoore parityBody True) lOutsTgt
      sqOutsTgt = scan (bodyToMoore (sqTgt sq) (1, True)) xs
   in sqOutsSrc == counterOuts && sqOutsTgt == parityOuts

-- | Square-preservation check: left whisker yields a commuting square.
leftWhiskerSquareOk :: Bool
leftWhiskerSquareOk =
  let sq = leftWhisker leftWhiskerBody counterToParitySq
   in all
        (\((s, n), x) -> downThenAcross sq ((s, n), x) == acrossThenDown sq ((s, n), x))
        [((s, n), x) | s <- carrierRange, n <- carrierRange, x <- [0, 1]]

-- | Observational horizontal-composition oracle, source and target sides.
hcomposeObservationalOk :: [Bool] -> Bool
hcomposeObservationalOk rs =
  let sq = hcompose echoSq counterToParitySq
      counterOuts = scan (bodyToMoore counterBody 2) rs
      echoOutsSrc = scan (bodyToMoore echoBody (-3)) counterOuts
      sqOutsSrc = scan (bodyToMoore (sqSrc sq) (2, -3)) rs
      parityOuts = scan (bodyToMoore parityBody False) rs
      echoOutsTgt = scan (bodyToMoore echoParityBody True) parityOuts
      sqOutsTgt = scan (bodyToMoore (sqTgt sq) (False, True)) rs
   in sqOutsSrc == echoOutsSrc && sqOutsTgt == echoOutsTgt

-- | Square-preservation check: horizontal composition yields a commuting square.
hcomposeSquareOk :: Bool
hcomposeSquareOk =
  let sq = hcompose echoSq counterToParitySq
   in all
        (\((n, s), r) -> downThenAcross sq ((n, s), r) == acrossThenDown sq ((n, s), r))
        [((n, s), r) | n <- carrierRange, s <- carrierRange, r <- [False, True]]

-- | Independently implemented middle body for the vertical-composition chain.
-- It is extensionally equal to 'mod4Body' but written differently, so the side
-- condition assertion compares two implementations rather than a binding to
-- itself.
mod4BodyB :: Body (,) Int (->) Bool Char
mod4BodyB = Body $ \(n, r) ->
  let n' = if r then 0 else cycleNext n
      cycleNext m = case m `mod` 4 of
        0 -> 1
        1 -> 2
        2 -> 3
        _ -> 0
   in (n', if odd n' then 'x' else 'y')

-- | Chain of two genuine quotients, Int -> Z4 -> Bool, for vertical
-- composition.  @mod4Body@ keeps the carrier in @[0..3]@.
mod4Body :: Body (,) Int (->) Bool Char
mod4Body = Body $ \(n, r) -> let n' = (if r then 0 else n + 1) `mod` 4 in (n', if odd n' then 'x' else 'y')

sqA :: Sq (,) (->) Int Int Bool Char
sqA = Sq (`mod` 4) counterBody mod4Body

sqB :: Sq (,) (->) Int Bool Bool Char
sqB = Sq odd mod4BodyB parityBody

-- | The middle body of the vertical composite matches on both sides of the
-- shared carrier.  This turns the silent 'vcomp' precondition into a checked
-- one at the call site.
vcompSideConditionOk :: Bool
vcompSideConditionOk =
  all
    (\(n, r) -> morphism (sqTgt sqA) (n, r) == morphism (sqSrc sqB) (n, r))
    [(n, r) | n <- carrierRange, r <- [False, True]]

-- | Vertical composition preserves commutation.
vcompOk :: Bool
vcompOk =
  let sq = vcomp sqB sqA
   in all
        (\(n, r) -> downThenAcross sq (n, r) == acrossThenDown sq (n, r))
        [(n, r) | n <- carrierRange, r <- [False, True]]

-- | The module-level sampled checker agrees with the commuting witness and
-- rejects the one-token perturbation.
checkSqOk :: Bool
checkSqOk =
  let samples = [(n, r) | n <- carrierRange, r <- [False, True]]
   in checkSq samples counterToParitySq
        && not (checkSq samples brokenSq)

-- | Vertical composition with deliberately different middles must fail the
-- sampled check.  Same-carrier factors put the middle on the composite's
-- own legs, so the mismatch is visible there; with distinct outer carriers
-- the composite's paths never touch the middle (see the 'vcomp' haddock),
-- which is exactly why the raw operator keeps its caller side condition.
checkSqVcompMismatchedOk :: Bool
checkSqVcompMismatchedOk =
  let samples = [(n, r) | n <- carrierRange, r <- [False, True]]
      agreed = vcomp (idSq mod4BodyB) (idSq mod4Body)
      mismatched = vcomp (idSq brokenBody) (idSq mod4Body)
   in checkSq samples agreed && not (checkSq samples mismatched)

-- | Left unitor proof witness: composing @counterBody@ with the identity at
-- the unit carrier is isomorphic to @counterBody@ itself.
unitorLeftOk :: Bool
unitorLeftOk =
  let sq = unitorLeftSq counterBody
   in all
        (\(n, r) -> downThenAcross sq (((), n), r) == acrossThenDown sq (((), n), r))
        [(n, r) | n <- carrierRange, r <- [False, True]]

-- | Right unitor proof witness.
unitorRightOk :: Bool
unitorRightOk =
  let sq = unitorRightSq counterBody
   in all
        (\(n, r) -> downThenAcross sq ((n, ()), r) == acrossThenDown sq ((n, ()), r))
        [(n, r) | n <- carrierRange, r <- [False, True]]

-- | Associator proof witness: carrier bracketing of three composed bodies is
-- isomorphic.  This also stress-tests 'seqCompose' asymmetrically.
associatorOk :: Bool
associatorOk =
  let sq = associatorSq maxBody sumBody delayBody
   in all
        (\input -> downThenAcross sq input == acrossThenDown sq input)
        [(((s1, s2), s3), a) | s1 <- smallRange, s2 <- smallRange, s3 <- smallRange, a <- smallRange]

-- | Cross-class coherence: for @(,)@ and @(->)@, 'strength' must agree with
-- @tensor id@.  If this fails for an instance, the two halves of the module
-- disagree about what whiskering means.
strengthCoherenceOk :: Bool
strengthCoherenceOk =
  let f = (+ 1) :: Int -> Int
   in and
        [ strength f (s, x) == tensor id f (s, x)
        | s <- smallRange,
          x <- smallRange
        ]

-- | Boundary whisker preserves the square.
whiskerSqSquareOk :: Bool
whiskerSqSquareOk =
  let sq = whiskerSq boundaryF boundaryG counterToParitySq
   in all
        (\(n, r) -> downThenAcross sq (n, r) == acrossThenDown sq (n, r))
        [(n, r) | n <- carrierRange, r <- [0, 1, 2, 3]]

-- * Feedback-category law oracles

--
-- These check the guarded feedback operator 'feedbackBody' against the
-- feedback-category axioms of Di Lavore et al., "Span(Graph): a Canonical
-- Feedback Algebra of Open Transition Systems" (arXiv:2010.10069), §3.1:
-- A1 tightening, A2 vanishing, A3 joining, A4 strength/superposing, A5 sliding
-- (isomorphisms only).  Yanking is /not/ an axiom; we assert that it fails.

-- | Body-level feedback: reassociate so the feedback wire becomes part of
-- the carrier, which grows from @ch@ to @t ch s@ and stays explicit.
feedbackBody :: (Assoc t arr) => Body t ch arr (t s a) (t s b) -> Body t (t ch s) arr a b
feedbackBody (Body f) = Body (assoc .> f .> assoc')

-- | Parallel (tensor) composition of two bodies at the body level.  This is
-- the pointed counterpart to the tensor of loose 1-cells used in the
-- superposing and tightening laws.
tensorBody ::
  Body (,) ch1 (->) a b ->
  Body (,) ch2 (->) c d ->
  Body (,) (ch1, ch2) (->) (a, c) (b, d)
tensorBody (Body f) (Body g) =
  Body $ \((ch1, ch2), (a, c)) ->
    let (ch1', b) = f (ch1, a)
        (ch2', d) = g (ch2, c)
     in ((ch1', ch2'), (b, d))

-- | Identity body at the unit carrier.
idBody :: Body (,) () (->) a a
idBody = Body $ \((), a) -> ((), a)

-- | Running-sum body before feedback: state accumulates the input and the
-- output is the new state.
runningSumFB :: Body (,) () (->) (Int, Int) (Int, Int)
runningSumFB = Body $ \((), (s, a)) -> let s' = s + a in ((), (s', s'))

-- | Behaviour oracle: a running-sum feedback circuit produces the cumulative
-- sums [1,3,6] on input [1,2,3].
runningSumFeedbackOk :: Bool
runningSumFeedbackOk =
  scan (bodyToMoore (feedbackBody runningSumFB) ((), 0)) [1, 2, 3] == [1, 3, 6]

-- | Body used in the vanishing law: increment the payload while carrying the
-- unit feedback wire.
vanishingFBody :: Body (,) () (->) ((), Int) ((), Int)
vanishingFBody = Body $ \((), ((), a)) -> ((), ((), a + 1))

-- | Direct implementation of the same map without feedback.
vanishingDirectBody :: Body (,) () (->) Int Int
vanishingDirectBody = Body $ \((), a) -> ((), a + 1)

-- | A2 Vanishing: feedback over the unit object @()@ is the identity.
vanishingOk :: Bool
vanishingOk =
  scan (bodyToMoore (feedbackBody vanishingFBody) ((), ())) [1, 2, 3]
    == scan (bodyToMoore vanishingDirectBody ()) [1, 2, 3]

-- | Post-feedback map used in the tightening law: add ten to the output.
tighteningHBody :: Body (,) () (->) Int Int
tighteningHBody = Body $ \((), x) -> ((), x + 10)

-- | A1 Tightening: @feedback ((id_s \\otimes h) \\circ f) = h \\circ feedback f@.
tighteningOk :: Bool
tighteningOk =
  let idS = idBody :: Body (,) () (->) Int Int
      lhs = feedbackBody ((idS `tensorBody` tighteningHBody) `seqCompose` runningSumFB)
      rhs = tighteningHBody `seqCompose` feedbackBody runningSumFB
   in scan (bodyToMoore lhs (((), ((), ())), 0)) [1, 2, 3]
        == scan (bodyToMoore rhs (((), 0), ())) [1, 2, 3]

-- | Body used in the joining law: two accumulators @(s,t)@ with output @t'@.
joiningFBody :: Body (,) () (->) ((Int, Int), Int) ((Int, Int), Int)
joiningFBody = Body $ \((), ((s, t), a)) ->
  let s' = s + a; t' = t + s' in ((), ((s', t'), t'))

-- | Reassociate @((s, t), a)@ to @(s, (t, a))@ so that feedback can be applied
-- over @s@ first, leaving @(t, a)@ as the payload for a second feedback.
joiningReassocBody :: Body (,) () (->) (Int, (Int, Int)) (Int, (Int, Int))
joiningReassocBody =
  Body $ \((), (s, (t, a))) ->
    let ((), ((s', t'), b)) = morphism joiningFBody ((), ((s, t), a))
     in ((), (s', (t', b)))

-- | A3 Joining: nested feedback over @(s, t)@ equals single feedback over the
-- pair.  The two sides have carriers @((ch, s), t)@ and @(ch, (s, t))@, so the
-- oracle compares observational outputs.
joiningOk :: Bool
joiningOk =
  let joiningFBOnce :: Body (,) ((), Int) (->) (Int, Int) (Int, Int)
      joiningFBOnce = feedbackBody joiningReassocBody
      joiningFBTwice :: Body (,) (((), Int), Int) (->) Int Int
      joiningFBTwice = feedbackBody joiningFBOnce
   in scan (bodyToMoore joiningFBTwice (((), 0), 0)) [1, 2, 3]
        == scan (bodyToMoore (feedbackBody joiningFBody) ((), (0, 0))) [1, 2, 3]

-- | Body used in the superposing law: add 100 to the parallel stream.
superposingGBody :: Body (,) () (->) Int Int
superposingGBody = Body $ \((), x) -> ((), x + 100)

-- | Reassociate @((s, a), c)@ to @(s, (a, c))@ so that feedback over @s@ can
-- be applied to the tensor @f \\otimes g@.
superposingLhsBody :: Body (,) ((), ()) (->) (Int, (Int, Int)) (Int, (Int, Int))
superposingLhsBody =
  Body $ \(((), ()), (s, (a, c))) ->
    let (((), ()), ((s', b), d)) = morphism (runningSumFB `tensorBody` superposingGBody) (((), ()), ((s, a), c))
     in (((), ()), (s', (b, d)))

-- | A4 Strength / superposing: @feedback f \\otimes g = feedback (f \\otimes g)@.
superposingOk :: Bool
superposingOk =
  let lhs = feedbackBody superposingLhsBody
      rhs = feedbackBody runningSumFB `tensorBody` superposingGBody
   in scan (bodyToMoore lhs (((), ()), 0)) [(1, 10), (2, 20), (3, 30)]
        == scan (bodyToMoore rhs (((), 0), ())) [(1, 10), (2, 20), (3, 30)]

-- | Isomorphism used in the sliding law: shift state by one.
slidingHBody :: Body (,) () (->) Int Int
slidingHBody = Body $ \((), s) -> ((), s + 1)

-- | Body used in the sliding law: input state is @t@, output state is @t+a@.
slidingFBody :: Body (,) () (->) (Int, Int) (Int, Int)
slidingFBody = Body $ \((), (t, a)) -> let s' = t + a in ((), (s', s'))

-- | A5 Sliding: for an isomorphism @h : s -> t@,
-- @feedback_s (f \\circ (h \\otimes id)) = feedback_t ((h \\otimes id) \\circ f)@.
slidingOk :: Bool
slidingOk =
  let hTensorId = slidingHBody `tensorBody` idBody
      lhs = feedbackBody (slidingFBody `seqCompose` hTensorId)
      rhs = feedbackBody (hTensorId `seqCompose` slidingFBody)
   in scan (bodyToMoore lhs ((((), ()), ()), 0)) [1, 2, 3]
        == scan (bodyToMoore rhs (((), ((), ())), 1)) [1, 2, 3]

-- | Braid on @(s, s)@ used to show yanking fails.
feedbackBraidBody :: Body (,) () (->) (Int, Int) (Int, Int)
feedbackBraidBody = Body $ \((), (x, y)) -> ((), (y, x))

-- | Yanking is /not/ required in a feedback category.  Feedback of the braid
-- on @(s, s)@ yields a one-step delay, not the identity.
yankingFailsOk :: Bool
yankingFailsOk =
  let fbBraid = feedbackBody feedbackBraidBody
   in scan (bodyToMoore fbBraid ((), 0)) [1, 2, 3] /= [1, 2, 3]
        && scan (bodyToMoore fbBraid ((), 0)) [1, 2, 3] == [0, 1, 2]

-- * Either carrier oracles

-- | A simple 'Either' body: a loop that counts down from @n@ to @0@ and
-- returns @0@.  The carrier is 'Int': the current count.
countdownBody :: Body Either Int (->) Int Int
countdownBody = Body $ \case
  Right n -> Left n
  Left 0 -> Right 0
  Left m -> Left (m - 1)

-- | Behaviour oracle: the countdown flowchart halts with the expected value.
eitherBehaviourOk :: Bool
eitherBehaviourOk =
  fst (runFlowchart countdownBody 20 5) == Just 0
    && fst (runFlowchart countdownBody 20 0) == Just 0
    && isNothing (fst (runFlowchart countdownBody 2 5))

-- | 'strength' for 'Either' is functorial action, which must agree with
-- @tensor id@.
eitherStrengthCoherenceOk :: Bool
eitherStrengthCoherenceOk =
  let f = (+ 1) :: Int -> Int
      space = [Left 'a', Right 0, Right 1, Left 'b']
   in all (\x -> strength f x == tensor id f x) space

-- | Body for the 'Either' unitor witnesses.  Carrier is 'Bool', so the
-- unitors are tested on inputs that actually carry a non-trivial state.
eitherUnitorBody :: Body Either Bool (->) Int Int
eitherUnitorBody = Body $ \case
  Right n -> Right (n + 1)
  Left b -> Left (not b)

-- | Left-unitor witness for 'Either': composing with the identity at the
-- unit carrier ('Void') is isomorphic to the original body.
eitherUnitorLeftOk :: Bool
eitherUnitorLeftOk =
  let sq = unitorLeftSq eitherUnitorBody
   in all
        (\x -> downThenAcross sq x == acrossThenDown sq x)
        [Right 0, Right 1, Right 2, Left (Right True), Left (Right False)]

-- | Right-unitor witness for 'Either'.
eitherUnitorRightOk :: Bool
eitherUnitorRightOk =
  let sq = unitorRightSq eitherUnitorBody
   in all
        (\x -> downThenAcross sq x == acrossThenDown sq x)
        [Right 0, Right 1, Right 2, Left (Left True), Left (Left False)]

-- | Bodies for the 'Either' associativity oracle.  @eitherFBody@ can loop;
-- @eitherGBody@ and @eitherHBody@ always halt.  The oracle checks that the
-- two carrier bracketings agree on inputs that exercise all three paths
-- (straight through, f-loop, g-loop).
eitherFBody :: Body Either Bool (->) Int Int
eitherFBody = Body $ \case
  Right 0 -> Left True
  Right n -> Right n
  Left True -> Right 0
  Left False -> Right 1

eitherGBody :: Body Either () (->) Int Int
eitherGBody = Body $ \case
  Right n | n < 0 -> Left ()
  Right n -> Right (n + 10)
  Left () -> Right 99

eitherHBody :: Body Either () (->) Int Int
eitherHBody = Body $ \case
  Right n -> Right (n * 2)
  Left () -> Right 999

-- | Associativity oracle for 'Either' cascade, using observational halting
-- equality.  The two sides have carriers @((ch1 + ch2) + ch3)@ and
-- @(ch1 + (ch2 + ch3))@, so the check is up to carrier isomorphism.
eitherCascadeAssocOk :: Bool
eitherCascadeAssocOk =
  let lhs = seqCompose eitherHBody (seqCompose eitherGBody eitherFBody)
      rhs = seqCompose (seqCompose eitherHBody eitherGBody) eitherFBody
   in all
        ( \n ->
            fst (runFlowchart lhs 30 n)
              == fst (runFlowchart rhs 30 n)
        )
        [5, 0, -1]

-- * Elgot dagger / feedback-at-Either oracles

-- | Helper: run the Elgot dagger of @f :: a -> Either a b@ with a fuel bound.
--
-- The dagger is direct fuel-bounded 'Either' iteration: feed 'Left' back in,
-- 'Right' halts, fuel decrements per step.  (The retired elgot gadget was
-- pinned against this runner before deletion — same result, same step count.)
-- A flowchart has no stored state, so the input @a0@ is the only initial
-- value; there is no separate seed.
runElgot :: (a -> Either a b) -> Int -> a -> (Maybe b, Int)
runElgot f fuel0 a0 = go fuel0 0 a0
  where
    go 0 steps _ = (Nothing, steps)
    go n steps a = case f a of
      Left a' -> go (n - 1) (steps + 1) a'
      Right b -> (Just b, steps + 1)

-- | A1 Fixed point: @f^\\dagger(a) = [id, f^\\dagger](f(a))@.
--
-- The step count is not part of the law, so only the result @Maybe b@ is
-- compared.
elgotFixedPointOk :: Bool
elgotFixedPointOk =
  let f :: Int -> Either Int Int
      f n = if n <= 0 then Right (n * 10) else Left (n - 1)
      eval a = case f a of
        Left s -> fst (runElgot f 19 s)
        Right b -> Just b
   in all (\n -> fst (runElgot f 20 n) == eval n) [0, 1, 2, 3, 4, 5]

-- | A2 Naturality: for @g :: b -> c@, @((id + g) \\circ f)^\\dagger = g \\circ f^\\dagger@.
--
-- Only the result @Maybe c@ is compared; the step counts differ because @g@ is
-- applied after the iteration on the right-hand side.
elgotNaturalityOk :: Bool
elgotNaturalityOk =
  let f :: Int -> Either Int Int
      f n = if n <= 0 then Right (n * 10) else Left (n - 1)
      g = (+ 100)
      f' n = case f n of
        Left s -> Left s
        Right b -> Right (g b)
   in all (\n -> fst (runElgot f' 20 n) == (g <$> fst (runElgot f 20 n))) [0, 1, 2, 3, 4, 5]

-- | Yanking at 'Either': feedback of the swap on @s + s@.  Unlike the
-- product case, this halts with the input unchanged, so yanking holds for
-- the coproduct symmetry.
--
-- The step count is part of the claim: the swap must take exactly two steps
-- (round-trip through the loop), not one.  Deleting the swap and replacing it
-- with the identity yields @(Just 5, 1)@ and fails this oracle.
eitherYankOk :: Bool
eitherYankOk =
  let swapBody :: Body Either Void (->) (Either Int Int) (Either Int Int)
      swapBody =
        Body $ \case
          Right (Left s) -> Right (Right s)
          Right (Right s) -> Right (Left s)
          Left v -> absurd v
      yankBody = Body $ assoc .> morphism swapBody .> assoc'
   in runFlowchart yankBody 10 5 == (Just 5, 2)
        && runFlowchart yankBody 10 7 == (Just 7, 2)

-- * Uniformity / dinaturality oracles for Either feedback

-- | Helper: extract the payload function of a body whose carrier is 'Void'.
-- Such a body is essentially a function on its payload, because @Either Void x@
-- is isomorphic to @x@.
runVoidBody :: Body Either Void (->) a b -> a -> b
runVoidBody b a = case morphism b (Right a) of
  Right b' -> b'
  Left v -> absurd v

-- | Uniformity: a non-injective two-cell makes feedback invariant under a
-- genuine quotient of the feedback wire.  The source feedback wire is 'Int';
-- the target is 'Bool' via @odd :: Int -> Bool@.  Both wires carry two
-- reachable values, and the halt value depends on which wire state the loop
-- halts from, so the test distinguishes "invariant under quotient" from
-- "invariant under collapse to a point".
--
-- The bodies are /open/: the feedback wire appears in the payload, so they
-- can be passed to 'feedbackBody'.  After feedback the carrier is
-- @Either Void (Either s a) ≅ Either s a@, explicit in the type.
uniformitySourceOpen :: Body Either Void (->) (Either Int Int) (Either Int Int)
uniformitySourceOpen =
  Body $ \case
    Right (Right a) -> Right (Left a)
    Right (Left n) -> Right (Right (if odd n then 7 else 9))
    Left v -> absurd v

uniformityTargetOpen :: Body Either Void (->) (Either Bool Int) (Either Bool Int)
uniformityTargetOpen =
  Body $ \case
    Right (Right a) -> Right (Left (odd a))
    Right (Left b) -> Right (Right (if b then 7 else 9))
    Left v -> absurd v

-- | Uniformity hypothesis on the open bodies: quotienting the feedback wire
-- with @odd@ commutes with the two bodies.
eitherUniformityHypothesisOk :: Bool
eitherUniformityHypothesisOk =
  let h = odd :: Int -> Bool
      srcFun = runVoidBody uniformitySourceOpen
      tgtFun = runVoidBody uniformityTargetOpen
   in all
        ( \x ->
            first h (srcFun x)
              == tgtFun (first h x)
        )
        [Right 0, Right 1, Right 2, Left 0, Left 1, Left 2]

-- | Uniformity conclusion: feedback of the two open bodies has the same trace.
eitherUniformityOk :: Bool
eitherUniformityOk =
  let srcClosed = feedbackBody uniformitySourceOpen
      tgtClosed = feedbackBody uniformityTargetOpen
      traceOk =
        all
          (\n -> fst (runFlowchart srcClosed 10 n) == fst (runFlowchart tgtClosed 10 n))
          [0, 1, 2, 3]
   in eitherUniformityHypothesisOk && traceOk

-- | A three-element cyclic group for the sliding witness.  We need an
-- isomorphism that is not self-inverse; 'Bool' has only identity, negation,
-- and constants, so it cannot carry a non-involutive iso.
data Z3 = Z0 | Z1 | Z2 deriving (Eq, Show)

-- | Cyclic shift on 'Z3'.
nextZ3 :: Z3 -> Z3
nextZ3 Z0 = Z1
nextZ3 Z1 = Z2
nextZ3 Z2 = Z0

-- | Sliding (dinaturality) for an isomorphism on the feedback wire.  The body
-- steps through 'Z3' and halts with a value depending on the wire state, so
-- the wire is genuinely observed.  @nextZ3@ is a three-cycle, not an
-- involution, so applying it on the wrong side of the trace is observable.
eitherSlidingOk :: Bool
eitherSlidingOk =
  let f :: Body Either Void (->) (Either Z3 Int) (Either Z3 Int)
      f =
        Body $ \case
          Right (Right a) | even a -> Right (Left Z0)
          Right (Right _) -> Right (Left Z1)
          Right (Left Z0) -> Right (Right 10)
          Right (Left Z1) -> Right (Right 20)
          Right (Left Z2) -> Right (Right 30)
          Left v -> absurd v
      h :: Body Either Void (->) (Either Z3 Int) (Either Z3 Int)
      h =
        Body $ \case
          Right (Left z) -> Right (Left (nextZ3 z))
          Right (Right a) -> Right (Right a)
          Left v -> absurd v
      lhsOpen = Body $ morphism h .> morphism f
      rhsOpen = Body $ morphism f .> morphism h
      lhs = feedbackBody lhsOpen
      rhs = feedbackBody rhsOpen
   in all
        (\n -> fst (runFlowchart lhs 10 n) == fst (runFlowchart rhs 10 n))
        [0, 1, 2, 3]

-- * These carrier oracles

-- | 'strength' for 'These' is functorial action, which must agree with
-- @tensor id@.
theseStrengthCoherenceOk :: Bool
theseStrengthCoherenceOk =
  let f = (+ 1) :: Int -> Int
      space =
        [ This 'a',
          That 0,
          That 1,
          These 'b' 2,
          These 'c' (-1)
        ]
   in all (\x -> strength f x == tensor id f x) space

-- | Body for the left-unitor witness.  Carrier is 'Bool', so the source carrier
-- @These Void Bool@ has both payload-only and carrier-only shapes.
theseLeftUnitorBody :: Body These Bool (->) Int Int
theseLeftUnitorBody =
  Body $ \case
    This b -> This (not b)
    That n -> These True (n + 1)
    These b n -> These (not b) (n + 1)

-- | Left-unitor witness for 'These': composing with the identity at the unit
-- carrier ('Void') is isomorphic to the original body.
theseUnitorLeftOk :: Bool
theseUnitorLeftOk =
  let sq = unitorLeftSq theseLeftUnitorBody
      space = [That n | n <- [0, 1, 2]] ++ [This (That b) | b <- [False, True]]
   in all
        (\x -> downThenAcross sq x == acrossThenDown sq x)
        space

-- | Body for the right-unitor witness.  Carrier is @()@, so the source carrier
-- @These () Void@ has only the 'This ()' shape.
theseRightUnitorBody :: Body These () (->) Int Int
theseRightUnitorBody =
  Body $ \case
    This () -> This ()
    That n -> These () (n * 2)
    These () n -> These () (n * 2)

-- | Right-unitor witness for 'These'.
theseUnitorRightOk :: Bool
theseUnitorRightOk =
  let sq = unitorRightSq theseRightUnitorBody
      space = [That n | n <- [0, 1, 2]] ++ [This (This ())]
   in all
        (\x -> downThenAcross sq x == acrossThenDown sq x)
        space

-- | Bodies for the 'These' associativity oracle.  Each body touches both the
-- carrier and the payload, so mis-threaded carrier components are visible.
theseFBody :: Body These Bool (->) Int Int
theseFBody = theseLeftUnitorBody

theseGBody :: Body These () (->) Int Int
theseGBody = theseRightUnitorBody

theseHBody :: Body These Char (->) Int Int
theseHBody =
  Body $ \case
    This c -> This c
    That n -> These 'x' (n - 1)
    These c n -> These c (n - 1)

-- | Associativity oracle for 'These' cascade.  The two sides have carriers
-- @These (These Bool ()) Char@ and @These Bool (These () Char)@, so the check
-- is up to the 'These' associator.  The test space exercises all seven shapes
-- of the inclusive tensor.
theseCascadeAssocOk :: Bool
theseCascadeAssocOk =
  let sq = associatorSq theseHBody theseGBody theseFBody
      -- Source carrier is @These (These Bool ()) Char@; full input type is
      -- @These (These (These Bool ()) Char) Int@.  The eight shapes below
      -- exercise every constructor combination.
      shapes n b c =
        [ That n,
          This (That c),
          This (This (This b)),
          This (This (That ())),
          This (This (These b ())),
          This (These (This b) c),
          This (These (That ()) c),
          This (These (These b ()) c)
        ]
      space = concat [shapes n b c | n <- [-1, 0, 1], b <- [False, True], c <- ['x', 'y']]
   in all
        (\x -> downThenAcross sq x == acrossThenDown sq x)
        space

-- * Distributivity and derived-These oracles

-- | Left distributor round-trip.  The iso @(a, b + c) ≅ (a,b) + (a,c)@ is its
-- own inverse up to the class methods.
distlRoundTripOk :: Bool
distlRoundTripOk =
  let space = [(n, e) | n <- smallRange, e <- [Left 'a' :: Either Char Bool, Right False, Right True]]
      fwd = distl :: (Int, Either Char Bool) -> Either (Int, Char) (Int, Bool)
      bwd = distl' :: Either (Int, Char) (Int, Bool) -> (Int, Either Char Bool)
   in all (\x -> bwd (fwd x) == x) space
        && all ((\y -> fwd (bwd y) == y) . fwd) space

-- | Right distributor round-trip.
distrRoundTripOk :: Bool
distrRoundTripOk =
  let space = [(e, n) | e <- [Left 'a' :: Either Char Bool, Right False, Right True], n <- smallRange]
      fwd = distr :: (Either Char Bool, Int) -> Either (Char, Int) (Bool, Int)
      bwd = distr' :: Either (Char, Int) (Bool, Int) -> (Either Char Bool, Int)
   in all (\x -> bwd (fwd x) == x) space
        && all ((\y -> fwd (bwd y) == y) . fwd) space

-- | Isomorphism between hand-written 'These' and the distributive-derived
-- representation @a + b + a×b@.
theseToEither :: These a b -> Either a (Either b (a, b))
theseToEither = \case
  This a -> Left a
  That b -> Right (Left b)
  These a b -> Right (Right (a, b))

eitherToThese :: Either a (Either b (a, b)) -> These a b
eitherToThese = \case
  Left a -> This a
  Right (Left b) -> That b
  Right (Right (a, b)) -> These a b

-- | Reference 'tensor' for 'These' derived from @(,)@ and 'Either' via the
-- iso.  Uses only the base 'Tensor' instances, not the hand-written
-- 'Tensor These' instance.
refTheseTensor :: (a -> b) -> (c -> d) -> These a c -> These b d
refTheseTensor f g = eitherToThese . tensor f (tensor g (tensor f g)) . theseToEither

-- | Reference left unitor for 'These' derived from the base unitors and the
-- annihilator: @These Void a ≅ 0 + (a + 0×a) ≅ a@.
refTheseUnitl :: These Void a -> a
refTheseUnitl = either absurd (either id (absurd . fst)) . theseToEither

-- | Reference right unitor for 'These': @These a Void ≅ a + (0 + a×0) ≅ a@.
refTheseUnitr :: These a Void -> a
refTheseUnitr = either id (either absurd (absurd . snd)) . theseToEither

-- | Reference braid for 'These' derived from the iso.
refTheseBraid :: These a b -> These b a
refTheseBraid = eitherToThese . go . theseToEither
  where
    go (Left a) = Right (Left a)
    go (Right (Left b)) = Left b
    go (Right (Right (a, b))) = Right (Right (b, a))

-- | Reference 'strength' for 'These' derived from the iso.
refTheseStrength :: (b -> c) -> These a b -> These a c
refTheseStrength f = eitherToThese . go . theseToEither
  where
    go (Left a) = Left a
    go (Right (Left b)) = Right (Left (f b))
    go (Right (Right (a, b))) = Right (Right (a, f b))

-- | Nested iso for the derived 'These' associator: unfold the outer 'These',
-- then unfold the carrier inside the product/coproduct pieces.
theseToEitherNested ::
  These (These a b) c ->
  Either (Either a (Either b (a, b))) (Either c (Either a (Either b (a, b)), c))
theseToEitherNested x = case theseToEither x of
  Left y -> Left (theseToEither y)
  Right (Left c) -> Right (Left c)
  Right (Right (y, c)) -> Right (Right (theseToEither y, c))

-- | Convert the nested representation of @These a (These b c)@ into the
-- target iso @Either a (Either (These b c) (a, These b c))@.
theseAssocOut ::
  Either a (Either (Either b (Either c (b, c))) (a, Either b (Either c (b, c)))) ->
  Either a (Either (These b c) (a, These b c))
theseAssocOut (Left a) = Left a
theseAssocOut (Right (Left y)) = Right (Left (eitherToThese y))
theseAssocOut (Right (Right (a, y))) = Right (Right (a, eitherToThese y))

-- | Reference 'assoc' for 'These' derived from the distributive
-- representation.  Pattern-matches on the nested @(,)@ / 'Either' shape rather
-- than on 'These' constructors, so agreement with the hand-written instance is
-- a genuine cross-check.
refTheseAssoc :: These (These a b) c -> These a (These b c)
refTheseAssoc = eitherToThese . theseAssocOut . go . theseToEitherNested
  where
    go (Left (Left a)) = Left a
    go (Left (Right (Left b))) = Right (Left (Left b))
    go (Left (Right (Right (a, b)))) = Right (Right (a, Left b))
    go (Right (Left c)) = Right (Left (Right (Left c)))
    go (Right (Right (Left a, c))) = Right (Right (a, Right (Left c)))
    go (Right (Right (Right (Left b), c))) = Right (Left (Right (Right (b, c))))
    go (Right (Right (Right (Right (a, b)), c))) = Right (Right (a, Right (Right (b, c))))

-- | Nested iso for @These a (These b c)@.
theseToEitherNested' ::
  These a (These b c) ->
  Either a (Either (Either b (Either c (b, c))) (a, Either b (Either c (b, c))))
theseToEitherNested' x = case theseToEither x of
  Left a -> Left a
  Right (Left y) -> Right (Left (theseToEither y))
  Right (Right (a, y)) -> Right (Right (a, theseToEither y))

-- | Convert the nested representation of @These (These a b) c@ into the
-- target iso @Either (These a b) (Either c (These a b, c))@.
theseAssocPrimeOut ::
  Either (Either a (Either b (a, b))) (Either c (Either a (Either b (a, b)), c)) ->
  Either (These a b) (Either c (These a b, c))
theseAssocPrimeOut (Left y) = Left (eitherToThese y)
theseAssocPrimeOut (Right (Left c)) = Right (Left c)
theseAssocPrimeOut (Right (Right (z, c))) = Right (Right (eitherToThese z, c))

-- | Reference 'assoc'' for 'These' (inverse direction).
refTheseAssoc' :: These a (These b c) -> These (These a b) c
refTheseAssoc' = eitherToThese . theseAssocPrimeOut . go . theseToEitherNested'
  where
    go (Left a) = Left (Left a)
    go (Right (Left (Left b))) = Left (Right (Left b))
    go (Right (Left (Right (Left c)))) = Right (Left c)
    go (Right (Left (Right (Right (b, c))))) = Right (Right (Right (Left b), c))
    go (Right (Right (a, Left b))) = Left (Right (Right (a, b)))
    go (Right (Right (a, Right (Left c)))) = Right (Right (Left a, c))
    go (Right (Right (a, Right (Right (b, c))))) = Right (Right (Right (Right (a, b)), c))

-- | Convert the nested representation of @These b (These a c)@ into the
-- target iso @Either b (Either (These a c) (b, These a c))@.
theseSlideOut ::
  Either b (Either (Either a (Either c (a, c))) (b, Either a (Either c (a, c)))) ->
  Either b (Either (These a c) (b, These a c))
theseSlideOut (Left b) = Left b
theseSlideOut (Right (Left y)) = Right (Left (eitherToThese y))
theseSlideOut (Right (Right (b, y))) = Right (Right (b, eitherToThese y))

-- | Reference 'slide' for 'These' derived from the iso.
refTheseSlide :: These a (These b c) -> These b (These a c)
refTheseSlide = eitherToThese . theseSlideOut . go . theseToEitherNested'
  where
    go (Left a) = Right (Left (Left a))
    go (Right (Left (Left b))) = Left b
    go (Right (Left (Right (Left c)))) = Right (Left (Right (Left c)))
    go (Right (Left (Right (Right (b, c))))) = Right (Right (b, Right (Left c)))
    go (Right (Right (a, Left b))) = Right (Right (b, Left a))
    go (Right (Right (a, Right (Left c)))) = Right (Left (Right (Right (a, c))))
    go (Right (Right (a, Right (Right (b, c))))) = Right (Right (b, Right (Right (a, c))))

-- | Hand-written 'Tensor These' agrees with the reference derived from @(,)@
-- and 'Either'.
derivedTheseTensorOk :: Bool
derivedTheseTensorOk =
  let f = (+ 1) :: Int -> Int
      g = not
      space = [This 0, This 1, That False, That True, These 0 False, These 1 True]
   in all (\x -> refTheseTensor f g x == tensor f g x) space

-- | Hand-written left unitor agrees with the derived reference.  @These Void a@
-- is inhabited only through 'That', since 'This' and 'These' require a 'Void'.
derivedTheseUnitlOk :: Bool
derivedTheseUnitlOk =
  let space = [That n | n <- [0, 1, 2]] :: [These Void Int]
   in all (\x -> refTheseUnitl x == unitl x) space

-- | Hand-written right unitor agrees with the derived reference.  @These a Void@
-- is inhabited only through 'This'.
derivedTheseUnitrOk :: Bool
derivedTheseUnitrOk =
  let space = [This n | n <- [0, 1, 2]] :: [These Int Void]
   in all (\x -> refTheseUnitr x == unitr x) space

-- | Hand-written 'Action These' braid agrees with the derived reference.
derivedTheseBraidOk :: Bool
derivedTheseBraidOk =
  let space = [This 0, This 1, That 'a', That 'b', These 0 'a', These 1 'b'] :: [These Int Char]
   in all (\x -> refTheseBraid x == braid x) space

-- | Hand-written 'Strength These' agrees with the derived reference.
derivedTheseStrengthOk :: Bool
derivedTheseStrengthOk =
  let f = (+ 1) :: Int -> Int
      space = [This 'a', That 0, That 1, These 'a' 0, These 'b' (-1)]
   in all (\x -> refTheseStrength f x == strength f x) space

-- | Hand-written 'Channel These' assoc agrees with the derived reference.
derivedTheseAssocOk :: Bool
derivedTheseAssocOk =
  let shapes n b c =
        [ That n,
          This (That c),
          This (This (This b)),
          This (This (That ())),
          This (This (These b ())),
          This (These (This b) c),
          This (These (That ()) c),
          This (These (These b ()) c)
        ] ::
          [These (These (These Bool ()) Char) Int]
      space = concat [shapes n b c | n <- [-1, 0, 1] :: [Int], b <- [False, True], c <- ['x', 'y']]
   in all (\x -> refTheseAssoc x == assoc x) space

-- | Hand-written 'Channel These' assoc' agrees with the derived reference.
derivedTheseAssocPrimeOk :: Bool
derivedTheseAssocPrimeOk =
  let shapes a b c =
        [ This a,
          That (This b),
          That (That c),
          That (These b c),
          These a (This b),
          These a (That c),
          These a (These b c)
        ] ::
          [These Bool (These () Char)]
      space = concat [shapes a b c | a <- [False, True], b <- [()], c <- ['x', 'y']]
   in all (\x -> refTheseAssoc' x == assoc' x) space

-- | Hand-written 'Channel These' slide agrees with the derived reference.
derivedTheseSlideOk :: Bool
derivedTheseSlideOk =
  let shapes a b c =
        [ This a,
          That (This b),
          That (That c),
          That (These b c),
          These a (This b),
          These a (That c),
          These a (These b c)
        ] ::
          [These Bool (These () Char)]
      space = concat [shapes a b c | a <- [False, True], b <- [()], c <- ['x', 'y']]
   in all (\x -> refTheseSlide x == slide x) space

-- * Bisimulation oracles

-- | Three-state body for the bisimulation witness.  States @1@ and @2@ are
-- behaviourally equivalent.
bisim3Body :: Body (,) Int (->) Bool Char
bisim3Body = Body $ \(s, r) ->
  case (s, r) of
    (0, False) -> (1, 'y')
    (0, True) -> (0, 'x')
    (1, False) -> (2, 'x')
    (1, True) -> (0, 'x')
    (2, False) -> (2, 'x')
    (2, True) -> (0, 'x')
    _ -> (0, 'x')

-- | Two-state body: the minimisation of 'bisim3Body'.  State @1@ corresponds
-- to both states @1@ and @2@ of the three-state machine.
bisim2Body :: Body (,) Int (->) Bool Char
bisim2Body = Body $ \(s, r) ->
  case (s, r) of
    (0, False) -> (1, 'y')
    (0, True) -> (0, 'x')
    (1, False) -> (1, 'x')
    (1, True) -> (0, 'x')
    _ -> (0, 'x')

-- | Bounded input alphabet for the finite-state bisimulation checks.
bisimInputs :: [Bool]
bisimInputs = [False, True]

-- | The maximal bisimulation between the three-state and two-state machines.
-- States @1@ and @2@ of the larger machine both collapse to state @1@ of the
-- smaller one.
bisimMaxOk :: Bool
bisimMaxOk =
  sort (maxBisimulation bisimInputs [0, 1, 2] [0, 1] bisim3Body bisim2Body)
    == sort [(0, 0), (1, 1), (2, 1)]

-- | The expected relation is itself a bisimulation.
bisimRelationOk :: Bool
bisimRelationOk =
  isBisimulation bisimInputs bisim3Body bisim2Body [(0, 0), (1, 1), (2, 1)]

-- | Initial states @0@ of the two machines are bisimilar.
bisimInitialStatesOk :: Bool
bisimInitialStatesOk =
  bisimilarStates bisimInputs [0, 1, 2] [0, 1] bisim3Body bisim2Body 0 0

-- | State @1@ of the three-state machine is not bisimilar to state @0@ of the
-- two-state machine (their outputs disagree on a non-reset step).
bisimNonEquivalentOk :: Bool
bisimNonEquivalentOk =
  not (bisimilarStates bisimInputs [0, 1, 2] [0, 1] bisim3Body bisim2Body 1 0)

-- | Behavioural agreement on an input stream: related initial states produce
-- identical outputs.
bisimStreamOk :: Bool
bisimStreamOk =
  scan (bodyToMoore bisim3Body 0) [False, True, False, False, True]
    == scan (bodyToMoore bisim2Body 0) [False, True, False, False, True]

-- | Carrier-isomorphism implies bisimulation, but not conversely.  Two
-- isomorphic two-state machines (states relabelled @10,11@ vs @0,1@) are
-- bisimilar via the renaming relation.
bisimCarrierIsoFinerOk :: Bool
bisimCarrierIsoFinerOk =
  let bodyA = bisim2Body
      bodyB :: Body (,) Int (->) Bool Char
      bodyB =
        Body $ \(s, r) ->
          case (s, r) of
            (10, False) -> (11, 'y')
            (10, True) -> (10, 'x')
            (11, False) -> (11, 'x')
            (11, True) -> (10, 'x')
            _ -> (10, 'x')
      rel :: [(Int, Int)]
      rel = [(0, 10), (1, 11)]
   in isBisimulation bisimInputs bodyA bodyB rel
        && bisimilarStates bisimInputs [0, 1] [10, 11] bodyA bodyB 0 10

-- | Exact oracle over a bounded input space.
--
-- Note: the two-cell tests only exercise 'tensor' in its first slot (the
-- carrier map), with the second slot fed 'id'.  Coverage of 'tensor's payload
-- slot belongs in "Axioma.Machine"; 'hcomposeObservationalOk' also exercises
-- the joint behaviour of 'tensor' through horizontal composition.
equipTopic :: Verbosity -> IO [Bool]
equipTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "Arrow-equipment oracles: squares, feedback laws, and carriers"
  sequence
    [ checkV verbosity "counter-to-parity square commutes over bounded inputs" $
        and
          [ downThenAcross counterToParitySq (n, r) == acrossThenDown counterToParitySq (n, r)
          | n <- carrierRange,
            r <- [False, True]
          ],
      checkV verbosity "broken observation disagrees at the named input (4, False)" $
        downThenAcross brokenSq (4, False) /= acrossThenDown brokenSq (4, False),
      checkV verbosity "reset drift disagrees at the named input (0, True)" $
        downThenAcross resetDriftSq (0, True) /= acrossThenDown resetDriftSq (0, True),
      checkV verbosity "pointed cascade agrees with stream composition" $
        cascadeStreamOk [3, 1, 4, 1, 5],
      checkV verbosity "pointed cascade is associative on input lists" $
        cascadeAssocOk [3, 1, 4, 1, 5],
      checkV verbosity "seqCompose agrees with reference implementation" $
        seqComposeAgreesOk [3, 1, 4, 1, 5],
      checkV verbosity "seqCompose left identity" $
        seqComposeLeftIdOk [3, 1, 4, 1, 5],
      checkV verbosity "seqCompose right identity" $
        seqComposeRightIdOk [3, 1, 4, 1, 5],
      checkV verbosity "right whisker agrees with stream composition" $
        rightWhiskerObservationalOk [False, True, True, False, True],
      checkV verbosity "right whisker preserves the square" rightWhiskerSquareOk,
      checkV verbosity "left whisker agrees with stream composition" $
        leftWhiskerObservationalOk [1, 2, 3, 4, 5],
      checkV verbosity "left whisker preserves the square" leftWhiskerSquareOk,
      checkV verbosity "horizontal composition agrees with stream composition" $
        hcomposeObservationalOk [False, True, True, False, True],
      checkV verbosity "horizontal composition preserves the square" hcomposeSquareOk,
      checkV verbosity "vcomp side condition holds over bounded inputs" vcompSideConditionOk,
      checkV verbosity "vertical composition preserves commutation" vcompOk,
      checkV verbosity "checkSq passes the commuting witness and rejects the perturbed square" checkSqOk,
      checkV verbosity "vcomp with mismatched middles fails the sampled check" checkSqVcompMismatchedOk,
      checkV verbosity "left unitor witness commutes" unitorLeftOk,
      checkV verbosity "right unitor witness commutes" unitorRightOk,
      checkV verbosity "associator witness commutes" associatorOk,
      checkV verbosity "strength coherence (strength f == tensor id f)" strengthCoherenceOk,
      checkV verbosity "boundary whisker preserves the square" whiskerSqSquareOk,
      checkV verbosity "Machine-split poles agree with the Moore bodies" polesMatchBodyOk,
      checkV verbosity "interchange law (source)" $
        all interchangeSourceOk [(n, r) | n <- carrierRange, r <- [0, 1, 2, 3]],
      checkV verbosity "interchange law (target)" $
        all interchangeTargetOk [(b, r) | b <- [False, True], r <- [0, 1, 2, 3]],
      checkV verbosity "feedback running-sum behaviour" runningSumFeedbackOk,
      checkV verbosity "feedback vanishing (A2)" vanishingOk,
      checkV verbosity "feedback tightening (A1)" tighteningOk,
      checkV verbosity "feedback joining (A3)" joiningOk,
      checkV verbosity "feedback superposing (A4)" superposingOk,
      checkV verbosity "feedback sliding (A5)" slidingOk,
      checkV verbosity "feedback yanking fails" yankingFailsOk,
      checkV verbosity "Either flowchart behaviour" eitherBehaviourOk,
      checkV verbosity "Either strength coherence (strength f == tensor id f)" eitherStrengthCoherenceOk,
      checkV verbosity "Either left unitor witness commutes" eitherUnitorLeftOk,
      checkV verbosity "Either right unitor witness commutes" eitherUnitorRightOk,
      checkV verbosity "Either cascade associativity" eitherCascadeAssocOk,
      checkV verbosity "Elgot fixed point" elgotFixedPointOk,
      checkV verbosity "Elgot naturality" elgotNaturalityOk,
      checkV verbosity "Either yanking (swap) halts with identity in two steps" eitherYankOk,
      checkV verbosity "Either uniformity: feedback respects non-injective two-cell" eitherUniformityOk,
      checkV verbosity "Either sliding (dinaturality) for isomorphism" eitherSlidingOk,
      checkV verbosity "These strength coherence (strength f == tensor id f)" theseStrengthCoherenceOk,
      checkV verbosity "These left unitor witness commutes" theseUnitorLeftOk,
      checkV verbosity "These right unitor witness commutes" theseUnitorRightOk,
      checkV verbosity "These cascade associativity" theseCascadeAssocOk,
      checkV verbosity "Distributive distl round-trip" distlRoundTripOk,
      checkV verbosity "Distributive distr round-trip" distrRoundTripOk,
      checkV verbosity "derived These tensor agrees with hand-written" derivedTheseTensorOk,
      checkV verbosity "derived These unitl agrees with hand-written" derivedTheseUnitlOk,
      checkV verbosity "derived These unitr agrees with hand-written" derivedTheseUnitrOk,
      checkV verbosity "derived These braid agrees with hand-written" derivedTheseBraidOk,
      checkV verbosity "derived These strength agrees with hand-written" derivedTheseStrengthOk,
      checkV verbosity "derived These assoc agrees with hand-written" derivedTheseAssocOk,
      checkV verbosity "derived These assoc' agrees with hand-written" derivedTheseAssocPrimeOk,
      checkV verbosity "derived These slide agrees with hand-written" derivedTheseSlideOk,
      checkV verbosity "bisimulation max relation (3-state vs 2-state)" bisimMaxOk,
      checkV verbosity "bisimulation relation check" bisimRelationOk,
      checkV verbosity "bisimilar initial states" bisimInitialStatesOk,
      checkV verbosity "non-bisimilar states are not related" bisimNonEquivalentOk,
      checkV verbosity "bisimilar machines agree on streams" bisimStreamOk,
      checkV verbosity "carrier-iso implies bisimulation" bisimCarrierIsoFinerOk
    ]

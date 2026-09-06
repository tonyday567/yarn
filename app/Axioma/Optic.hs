{-# LANGUAGE DataKinds #-}

-- | Optic oracles — mixed optics as residual maps.
--
-- Every positive family is paired with a perturbation, so that a passing
-- check is known not to be vacuous: an optic that fails the round-trip law, a
-- sample that discriminates, and a residual change that is nevertheless
-- observationally invisible.
module Axioma.Optic
  ( opticTopic,
  )
where

import Axioma.Common (Verbosity (..), checkV)
import Circuit.Body (Body (..), morphism)
import Circuit.Category (Category (..), (.>))
import Circuit.Equip (Poles (..), close)
import Circuit.Machine (Machine, machine, machineMorphism, machineObsWith, machineToPoles)
import Circuit.Optic
  ( Optic (..),
    composeOptic,
    identityOptic,
    lensAsOptic,
    opticAsLens,
    opticPoles,
    opticUpdate,
  )
import Circuit.Poly (Dir, Mono, Pos)
import Control.Monad (when)
import Data.Void (Void, absurd)
import Prelude hiding (id, (.))

-- * Cartesian witnesses

-- | Lens focusing the first component of a pair.  Residual: the second
-- component.
firstLens :: Optic (,) String (->) Int Int (Int, String) (Int, String)
firstLens = Optic (\(n, s) -> (s, n)) (\(s, n) -> (n, s))

-- | Lens focusing the second component of a pair.  Residual: the first
-- component.  Both legs are the identity because the residual is already in
-- the leading slot.
secondLens :: Optic (,) Int (->) String String (Int, String) (Int, String)
secondLens = Optic id id

-- | A well-typed optic that is /not/ lawful: the backward leg perturbs the
-- residual on the way out, so updating with the identity is not the identity.
--
-- This is the falsification artifact for the round-trip law.  'Optic' carries
-- no lawfulness condition, and the wiki's open thread — lawfulness as
-- coalgebra for the comonad induced by the round-trip witness — is exactly
-- the gap this witnesses.
badLens :: Optic (,) String (->) Int Int (Int, String) (Int, String)
badLens = Optic (\(n, s) -> (s, n)) (\(s, n) -> (n, s ++ "!"))

-- | Outer lens: focus the @(Int, Bool)@ half of a nested pair.
outerLens ::
  Optic (,) String (->) (Int, Bool) (Int, Bool) ((Int, Bool), String) ((Int, Bool), String)
outerLens = Optic (\(p, s) -> (s, p)) (\(s, p) -> (p, s))

-- | Inner lens: focus the @Int@ of an @(Int, Bool)@.
innerLens :: Optic (,) Bool (->) Int Int (Int, Bool) (Int, Bool)
innerLens = Optic (\(n, b) -> (b, n)) (\(b, n) -> (n, b))

-- * Cocartesian witness

-- | Prism matching the @Left@ branch.  The residual is the branch that did
-- not match.
--
-- @'Circuit.Tensor.Unit' 'Either'@ is uninhabited, which is what denied the
-- old @SomeBody@ pattern an identity.  'Optic' has no such problem: the
-- residual is produced by the forward leg, never stored.  The @Either@
-- identity oracle below is the observable consequence.
prismLeft :: Optic Either String (->) Int Int (Either Int String) (Either Int String)
prismLeft =
  Optic
    ( \case
        Left n -> Right n
        Right s -> Left s
    )
    ( \case
        Left s -> Right s
        Right n -> Left n
    )

-- * Helpers

incFocus :: Int -> Int
incFocus = (+ 1)

reverseFocus :: String -> String
reverseFocus = reverse

-- | Extensional agreement over a bounded sample.
sameOn :: (Eq r) => [s] -> (s -> r) -> (s -> r) -> Bool
sameOn xs f g = all (\x -> f x == g x) xs

-- | Bounded sample of the cartesian whole.
wholes :: [(Int, String)]
wholes = [(n, s) | n <- [0, 3, 7], s <- ["", "hello", "ab"]]

-- | Bounded sample of the nested whole.
nested :: [((Int, Bool), String)]
nested = [((n, b), s) | n <- [0, 3], b <- [True, False], s <- ["", "hi"]]

-- | Bounded sample of the sum whole.
branches :: [Either Int String]
branches = [Left 0, Left 3, Right "", Right "hi"]

opticTopic :: Verbosity -> IO [Bool]
opticTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "Optic oracles"
  sequence
    [ -- update action
      checkV verbosity "identity optic updates the focus unchanged" $
        opticUpdate (identityOptic :: Optic (,) () (->) Int Int Int Int) incFocus 3 == 4,
      checkV verbosity "firstLens updates the first component" $
        opticUpdate firstLens incFocus (3, "hello") == (4, "hello"),
      checkV verbosity "secondLens updates the second component" $
        opticUpdate secondLens reverseFocus (3, "hello") == (3, "olleh"),
      -- lens laws
      checkV verbosity "lens get-put (update with identity is identity)" $
        sameOn wholes (opticUpdate firstLens id) id,
      checkV verbosity "lens put-get (the written focus reads back)" $
        sameOn wholes (opticUpdate firstLens (const 9) .> fst) (const 9),
      checkV verbosity "lens put-put (the last write wins)" $
        sameOn
          wholes
          (opticUpdate firstLens (const 7) .> opticUpdate firstLens (const 9))
          (opticUpdate firstLens (const 9)),
      -- falsification: the laws above are not automatic
      checkV verbosity "an unlawful optic is well-typed and fails get-put" $
        not (sameOn wholes (opticUpdate badLens id) id),
      checkV verbosity "the unlawful optic still passes put-get (the failure is specific)" $
        sameOn wholes (opticUpdate badLens (const 9) .> fst) (const 9),
      -- composition
      checkV verbosity "opticUpdate is functorial through composeOptic" $
        sameOn
          nested
          (opticUpdate (composeOptic innerLens outerLens) incFocus)
          (opticUpdate outerLens (opticUpdate innerLens incFocus)),
      checkV verbosity "functoriality holds for the unlawful optic too (it is structural)" $
        sameOn
          wholes
          (opticUpdate (composeOptic identityOptic badLens) incFocus)
          (opticUpdate badLens incFocus),
      checkV verbosity "composeOptic right unit (identity on the inside)" $
        sameOn
          wholes
          (opticUpdate (composeOptic identityOptic firstLens) incFocus)
          (opticUpdate firstLens incFocus),
      checkV verbosity "composeOptic left unit (identity on the outside)" $
        sameOn
          wholes
          (opticUpdate (composeOptic firstLens identityOptic) incFocus)
          (opticUpdate firstLens incFocus),
      checkV verbosity "the nested sample discriminates (functoriality is not vacuous)" $
        not
          ( sameOn
              nested
              (opticUpdate (composeOptic innerLens outerLens) incFocus)
              (opticUpdate (composeOptic innerLens outerLens) (const 0))
          ),
      -- Either / prisms
      checkV verbosity "Either identity optic updates the focus unchanged" $
        opticUpdate (identityOptic :: Optic Either Void (->) Int Int Int Int) incFocus 3 == 4,
      checkV verbosity "prism updates the matching branch only" $
        sameOn
          branches
          (opticUpdate prismLeft incFocus)
          ( \case
              Left n -> Left (n + 1)
              Right s -> Right s
          ),
      checkV verbosity "prism get-put" $
        sameOn branches (opticUpdate prismLeft id) id,
      checkV verbosity "prism composition with the Either identity agrees" $
        sameOn
          branches
          (opticUpdate (composeOptic identityOptic prismLeft) incFocus)
          (opticUpdate prismLeft incFocus),
      -- the residual is a coend, not a product
      checkV verbosity "polynomial-lens round trip changes the residual but not the behaviour" $
        sameOn
          wholes
          (opticUpdate (lensAsOptic (opticAsLens firstLens)) incFocus)
          (opticUpdate firstLens incFocus),
      checkV verbosity "the round trip of the unlawful optic is still unlawful" $
        not
          ( sameOn
              wholes
              (opticUpdate (lensAsOptic (opticAsLens badLens)) id)
              id
          ),
      -- poles action
      checkV verbosity "opticPoles suffixes the backward leg onto the companion" $
        let p = Poles fst (\ch -> (ch, 7)) :: Poles String (->) (String, Int) (String, Int)
         in companion (opticPoles firstLens p) "hi" == (7, "hi"),
      checkV verbosity "opticPoles read pole agrees with the backward leg" $
        let p = Poles fst (\ch -> (ch, 7)) :: Poles String (->) (String, Int) (String, Int)
         in companion (opticPoles firstLens p) "hi" == opticBackward firstLens ("hi", 7),
      -- Equipment-optic coherence: the companion/conjoint poles of a
      -- Machine are the opticPoles action of the diagonal machine optic
      -- (residual = machine state) on the stepping base pole.  The two
      -- sides are defined independently — machineToPoles hand-rolls its
      -- legs in Circuit.Machine, the optic path assembles iomap primitives —
      -- so the witness pins a real configuration: a mutation to either
      -- side's leg wiring (probe read, unstepped write) fails the sample
      -- agreement.
      checkV verbosity "machineToPoles agrees with the opticPoles action of the diagonal machine optic" $
        let stepInc (s, d) = case d of
              Left v -> absurd v
              Right i -> (s + i, (s * 2, ()))
            inc = machine stepInc :: Machine (,) Int (->) (Mono Int Int)
            optic ::
              Optic (,) Int (Body (,) Int (->)) (Dir (Mono Int Int)) () (Dir (Mono Int Int)) (Pos (Mono Int Int))
            optic =
              Optic
                (Body (\(s, d) -> (s, (s, d))))
                (Body (\(s0, (ch, ())) -> (s0, (ch * 2, ()))))
            base ::
              Poles Int (Body (,) Int (->)) (Int, Dir (Mono Int Int)) (Int, ())
            base =
              Poles
                (Body (\(s', (s'', d)) -> (fst (machineMorphism inc (s'', d)), fst (machineMorphism inc (s'', d)))))
                (Body (\(s, ch) -> (s, (ch, ()))))
            lhs = machineToPoles (machineObsWith (\s -> (s * 2, ())) inc)
            rhs = opticPoles optic base
            sample1 = morphism (close lhs) (3, Right 5) :: (Int, (Int, ()))
            sample2 = morphism (close rhs) (3, Right 5) :: (Int, (Int, ()))
            sample3 = morphism (close lhs) (4, Right 1) :: (Int, (Int, ()))
            sample4 = morphism (close rhs) (4, Right 1) :: (Int, (Int, ()))
         in sample1 == sample2 && sample3 == sample4
    ]

{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}

-- |
-- Module      : ToHypH
-- Description : Catamorphism from Traced Mealy to HypH Mealy
--
-- Uses Data.Mealy (existential, with Pair' strict state).
--
-- = What this solves
--
-- Traced Mealy with a recursive interpreter has Rec{} in Core.
-- toHypH maps to HypH Mealy where Compose → zipper.
-- zipper is productive corecursion — no recursive interpreter.
--
-- = What this does NOT solve
--
-- Loop with strict c. The loopH lazy knot has the same structure
-- as Costrong.unfirst. Needs delay on the feedback wire for strict c.
--
-- = Theory
--
-- Fugal extension s♭(e, a::as) = s(e,a) :: s♭(d(e,a), as)
-- is exactly zipper unfolding. Compose → zipper is correct.
module ToHypH
  ( toHypH,
    liftH,
    loopH,
  )
where

import Control.Arrow
import Control.Arrow (Arrow (..))
import Control.Category (Category (..))
import Data.Mealy (Mealy (..), pattern M)
import Data.Profunctor
import Hyp (HypH (..), zipper)
import Traced (Traced (..))
import Prelude hiding (id, (.))

instance Arrow Mealy where
  arr f = M (\a -> f a) (\_ a -> f a) id
  first (M i s e) =
    M
      (\(a, c) -> (i a, c))
      (\(sa, c) (a, _) -> (s sa a, c))
      (\(sa, c) -> (e sa, c))

-- ---------------------------------------------------------------------------
-- idH: identity
-- ---------------------------------------------------------------------------

-- | Identity HypH Mealy.
-- ι idH :: Mealy (HypH Mealy a a) a
-- Run the dual's ι against idH to get the a, return it.
idH :: HypH Mealy a a
idH =
  HypH $
    M
      -- inject: HypH Mealy a a -> s
      -- Run ι h against idH to get an a, use as state
      (\h -> runDual h idH)
      -- step: ignore current state, run dual with idH
      (\_ h -> runDual h idH)
      -- extract: identity
      id
  where
    runDual :: HypH Mealy a a -> HypH Mealy a a -> a
    runDual h cont = case ι h of
      M di _ de -> de (di cont)

-- ---------------------------------------------------------------------------
-- liftH: lift a Mealy into HypH Mealy
-- ---------------------------------------------------------------------------

-- | Lift m :: Mealy a b into HypH Mealy a b.
-- The dual h :: HypH Mealy b a provides a's.
-- To get an a from h: run ι h against the current continuation.
-- m's state threads through the tower.
liftH :: Mealy a b -> HypH Mealy a b
liftH m = case m of
  M inject step extract ->
    let self =
          HypH $
            M
              -- inject: get a from dual, seed m's state
              (\h -> inject (getA h self))
              -- step: get a from dual, step m
              (\s h -> step s (getA h self))
              -- extract: m's extract
              extract
     in self
  where
    getA :: HypH Mealy b a -> HypH Mealy a b -> a
    getA h cont = case ι h of
      M di _ de -> de (di cont)

-- ---------------------------------------------------------------------------
-- loopH: feedback in HypH Mealy
-- ---------------------------------------------------------------------------

-- | Close feedback wire c.
-- Lazy knot — same structure as Costrong.unfirst.
-- Works when inject is lazy on c; needs delay for strict c.
loopH :: HypH Mealy (a, c) (b, c) -> HypH Mealy a b
loopH p =
  let self = HypH $ case ι p of
        M pi ps pe ->
          M
            -- inject: build dual HypH Mealy (b,c) (a,c) that feeds back c.
            -- pi :: HypH Mealy (b,c) (a,c) -> s
            -- We construct a dual that returns (a, c0) where c0 is lazy knot.
            ( \h ->
                let a = getA h self
                    dual = mkFeedback a c0 -- dual produces (a, c0)
                    s0 = pi dual
                    c0 = snd (pe s0) -- lazy knot: c0 from first extract
                 in s0
            )
            -- step: build new dual with updated c from current state
            ( \s h ->
                let a = getA h self
                    c = snd (pe s)
                    dual = mkFeedback a c
                 in ps s dual
            )
            -- extract: fst of pe
            (fst . pe)
   in self
  where
    getA :: HypH Mealy b a -> HypH Mealy a b -> a
    getA h cont = case ι h of
      M di _ de -> de (di cont)

    -- \| Construct a HypH Mealy (b,c) (a,c) that ignores its input
    -- and always produces (a, c) — the fixed feedback pair.
    mkFeedback :: a -> c -> HypH Mealy (b, c) (a, c)
    mkFeedback a c =
      HypH $
        M
          (\_ -> (a, c))
          (\_ _ -> (a, c))
          id

-- ---------------------------------------------------------------------------
-- toHypH: the catamorphism
-- ---------------------------------------------------------------------------

toHypH :: Traced Mealy a b -> HypH Mealy a b
toHypH Pure = idH
toHypH (Lift m) = liftH m
toHypH (Compose g h) = toHypH g `zipper` toHypH h
toHypH (Loop p) = loopH (toHypH p)

runHypH h = ι h (HypH runHypH)

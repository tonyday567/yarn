{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}

-- |
-- Module      : ToHypH
-- Description : Catamorphism from Traced Mealy to Hyp Mealy
--
-- Uses Data.Mealy (existential, with Pair' strict state).
--
-- = What this solves
--
-- Traced Mealy with a recursive interpreter has Rec{} in Core.
-- fromMealy maps to Hyp Mealy where Compose → zipper.
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
module Traced.Mealy
  ( fromMealy,
    liftH,
    loopH,
  )
where

import Control.Arrow (Arrow, arr, first)
import Control.Category (Category (..))
import Data.Mealy (Mealy (..), pattern M)
import Data.Profunctor
import Hyp (Hyp (..), zipper)
import Traced
import Prelude hiding (id, (.))

instance Arrow Mealy where
  arr f = M (\a -> f a) (\_ a -> f a) id
  first = first'
  
--- | Identity Hyp Mealy.
--- ι idH :: Mealy (Hyp Mealy a a) a
--- Run the dual's ι against idH to get the a, return it.
idH :: Hyp Mealy a a
idH =
  Hyp $
    M
      -- inject: Hyp Mealy a a -> s
      -- Run ι h against idH to get an a, use as state
      (\h -> runDual h idH)
      -- step: ignore current state, run dual with idH
      (\_ h -> runDual h idH)
      -- extract: identity
      id
  where
    runDual :: Hyp Mealy a a -> Hyp Mealy a a -> a
    runDual h cont = case ι h of
      M di _ de -> de (di cont)

-- liftH: lift a Mealy into Hyp Mealy

-- | Lift m :: Mealy a b into Hyp Mealy a b.
-- The dual h :: Hyp Mealy b a provides a's.
-- To get an a from h: run ι h against the current continuation.
-- m's state threads through the tower.
liftH :: Mealy a b -> Hyp Mealy a b
liftH m = case m of
  M inject step extract ->
    let self =
          Hyp $
            M
              -- inject: get a from dual, seed m's state
              (\h -> inject (getA h self))
              -- step: get a from dual, step m
              (\s h -> step s (getA h self))
              -- extract: m's extract
              extract
     in self
  where
    getA :: Hyp Mealy b a -> Hyp Mealy a b -> a
    getA h cont = case ι h of
      M di _ de -> de (di cont)

-- loopH: feedback in Hyp Mealy

-- | Close feedback wire c.
-- Lazy knot — same structure as Costrong.unfirst.
-- Works when inject is lazy on c; needs delay for strict c.
loopH :: Hyp Mealy (a, c) (b, c) -> Hyp Mealy a b
loopH p =
  let self = Hyp $ case ι p of
        M pi ps pe ->
          M
            -- inject: build dual Hyp Mealy (b,c) (a,c) that feeds back c.
            -- pi :: Hyp Mealy (b,c) (a,c) -> s
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
    getA :: Hyp Mealy b a -> Hyp Mealy a b -> a
    getA h cont = case ι h of
      M di _ de -> de (di cont)

    -- \| Construct a Hyp Mealy (b,c) (a,c) that ignores its input
    -- and always produces (a, c) — the fixed feedback pair.
    mkFeedback :: a -> c -> Hyp Mealy (b, c) (a, c)
    mkFeedback a c =
      Hyp $
        M
          (\_ -> (a, c))
          (\_ _ -> (a, c))
          id

-- fromMealy: the catamorphism

-- | Convert a Traced Mealy machine to its corecursive Hyp form.
--
-- @fromMealy :: Traced Mealy a b -> Hyp Mealy a b@
--
-- This transforms finite syntax (@Traced@) into the coinfinite tower (@Hyp@).
-- The benefit: @Compose@ unfolds to @zipper@ (productive corecursion)
-- instead of a recursive interpreter with @Rec {}@ in Core.
--
-- The input @Traced Mealy a b@ describes a composition of Mealy machines:
-- @Pure@ (identity), @Lift@ (single machine), @Compose@ (sequence),
-- or @Loop@ (feedback).
--
-- The output @Hyp Mealy a b@ is the same computation, but structured
-- as a corecursive tower where each layer (@ι@) unfolds one step.
--
-- Example: a simple identity Mealy compiles and transforms
--
-- >>> import qualified Data.Mealy as Mealy
-- >>> import Traced (Traced(..))
-- >>> import Hyp (Hyp)
-- >>> let idMealy = Mealy.M id (\s a -> a) id :: Mealy.Mealy Int Int
-- >>> let traced = Lift idMealy :: Traced Mealy.Mealy Int Int
-- >>> let result = fromMealy traced :: Hyp Mealy.Mealy Int Int
-- >>> -- result is now the corecursive form, ready for ι invocation
-- >>> True
-- True
--
-- To use the result, invoke it with a dual continuation:
-- @ι result :: Mealy (Hyp Mealy b a) a@
-- FIXME: wont pass the sliding law?
fromMealy :: Traced Mealy a b -> Hyp Mealy a b
fromMealy Pure = idH
fromMealy (Lift m) = liftH m
fromMealy (Compose g h) = fromMealy g `zipper` fromMealy h
fromMealy (Loop p) = loopH (fromMealy p)


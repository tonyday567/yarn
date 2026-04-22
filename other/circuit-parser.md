# Circuit Parser Combinators

An abstract parser combinator library implemented using Circuit.

Demonstrates the power of the abstraction: **the same Circuit definition can be interpreted as**:

1. **Pure deterministic state threading** (fast, linear, using `(,)` tensor)
2. **Full backtracking/nondeterminism** (using `Either` tensor + delimited continuations)
3. **Algebraic / coinductive semantics** (unfolded to Hyperfunction)

## Design

A `Parser` is a `Circuit` that threads input state `s` and produces parsed values `a`. The tensor `t` decides semantics:
- `(,)` → deterministic state threading
- `Either` → full backtracking via delimited continuations

## Implementation

```haskell
{-# LANGUAGE Arrows #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Circuit.Examples.CircuitParser where

import Circuit
import Circuit.GoI ()
import Hyp
import Control.Arrow (Kleisli (..), runKleisli)
import Data.Char (isDigit)
import Prelude hiding (id, (.))

-- | A Parser threads input state s and produces parsed values a.
--   The feedback channel (via tensor t) handles repetition and choice.

type Parser arr t s a = Circuit arr t (s, Maybe a) (s, Maybe a)

-- Basic token parsers
satisfy :: (Category arr) => (Char -> Bool) -> Parser arr t String Char
satisfy p = Lift $ \(s, _) -> case s of
  (c:cs) | p c -> (cs, Just c)
  _            -> (s, Nothing)

char :: (Category arr) => Char -> Parser arr t String Char
char c = satisfy (== c)

-- Repetition: many using Loop
many :: (Category arr, Trace arr t) => Parser arr t s a -> Parser arr t s [a]
many p = Loop $ \case
  Right (s, _)             -> (s, Just [])      -- no items yet, exit with empty
  Left (s, Just x)         -> (s, Just (x:[])) -- accumulate
  Left (s, Nothing)        -> (s, Just [])      -- failure, exit with what we have

-- Examples
digitParser :: Parser (->) (,) String Int
digitParser = Lift $ \(s, _) -> case s of
  (c:cs) | isDigit c -> (cs, Just (read [c]))
  _                  -> (s, Nothing)

numberParser :: Parser (->) (,) String Int
numberParser = Lift $ \(s, _) ->
  let (digits, rest) = span isDigit s
  in if null digits then (s, Nothing) else (rest, Just (read digits))

-- Run deterministic parser
parseState :: Parser (->) (,) s a -> s -> Maybe (s, a)
parseState p s0 = case run p (s0, Nothing) of
  (s, Just a) -> Just (s, a)
  _           -> Nothing

-- Demo
demoParser :: IO ()
demoParser = do
  putStrLn "=== Circuit Parser ==="
  print $ parseState numberParser "12345abc"   -- Just ("abc",12345)
  print $ parseState numberParser "no digits"  -- Nothing
```

## The Vision

This card sketches the potential: a single parser Circuit that can be:

1. **Executed deterministically** with the standard `(->)` Trace
2. **Run with backtracking** using `Kleisli IO` + delimited continuations (Either tensor)
3. **Unfolded algebraically** to a Hyperfunction for coinductive reasoning

The tensor is the *control flow* lever: it switches between these interpretations without changing the combinator logic.

## Status

⟝ This is **aspirational code** showing the design space. The implementation details (especially monad instances and choice operators) need refinement to work smoothly. The core insight—that Circuit abstracts over both the computation model *and* the control flow strategy—is the point.

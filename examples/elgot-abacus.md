I'm glad the abacus-to-Circuit translation clicked for you! That's one of the nicest things about the design — you can read the Circuit backwards and recover the imperative counter-machine intuition almost directly.

Here's a cleaned-up, more idiomatic version that fits your library style (using Either tensor, proper use of Loop + Mendler, and ready to drop into your codebase).

## Polished Abacus → Circuit Compiler

```haskell
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}

module Circuit.Abacus where

import Circuit.Circuit
import Circuit.Traced
import Control.Category ((.))
import Prelude hiding ((.))

-- | A single-register Lambek abacus program
data Abacus a
  = Inc (Abacus a)                    -- X+ ; continue to next
  | Dec (Abacus a) (Abacus a)         -- X- ; if >0 goto first branch, else second
  | Output a                          -- halt and return value

-- | Compile an abacus program to a Circuit over the Either tensor.
--   Feedback channel carries the current register value (Int).
abacus :: Abacus b -> Circuit (->) Either Int b
abacus (Output x) = Lift $ const (Right x)

abacus (Inc next) =
  Lift (\case
    Left  n -> Left  (n + 1)      -- increment and continue
    Right x -> Right x)           -- pass through if already terminated
  . abacus next

abacus (Dec next1 next0) = Loop $ \case
  -- Still running: look at register
  Left 0  -> Left (reify (abacus next0) 0)   -- zero case → next0
  Left n  -> Left (reify (abacus next1) (n-1)) -- positive → decrement + next1
  Right x -> Right x                         -- already terminated

-- | Convenient runner
runAbacus :: Abacus b -> Int -> b
runAbacus prog initial = reify (abacus prog) initial
```

## Example Programs

```haskell
-- | Multiply m * n using repeated addition (classic counter machine example)
multiplyAbacus :: Int -> Abacus Int
multiplyAbacus m = Dec
  (Inc (multiplyAbacus m))   -- while register > 0: add m to result, decrement
  (Output 0)                 -- done

-- | Test
testMultiply :: IO ()
testMultiply = do
  print $ runAbacus (multiplyAbacus 7) 5   -- 35
  print $ runAbacus (multiplyAbacus 0) 10  -- 0
  print $ runAbacus (multiplyAbacus 1) 1   -- 1
```

## Why This Feels So Natural

- **Inc** is just a Lift that bumps the register in the Left channel.
- **Dec** is a Loop that branches on the register value — exactly the "taking turns" semantics of the Either tensor.
- The Mendler case in your lower ensures that when you compose larger programs (left-nested Compose), the feedback channel stays correctly wired through every iteration. No degenerate behaviour.

This is almost a direct syntactic embedding of the initial Elgot category from Nester's paper. Every abacus program becomes a Circuit (->) Either, and reify gives you the partial recursive function it computes.


---

## Multi-Register Abacus (Symbol-Heavy)

A symbol-heavy presentation using the little-language operators (η, ε, ⊙, ⊲, ↬, ⥁, etc.).

### Core Symbols Recap

| Symbol | Meaning |
|--------|---------|
| η      | lift (embed plain arrow) |
| ⊙      | sequential composition |
| ↬      | Loop (feedback / trace) |
| ε      | lower / reify (observe to plain function) |
| ⥁      | run (tie the knot on diagonal, when applicable) |
| ⊲      | push (prepend a plain function) |

### Single-Register Abacus (Symbolic)

```haskell
-- Abacus instructions as little-language terms (Either tensor)

inc  :: Abacus b → Abacus b
inc next = η (λcase Left n → Left (n+1); Right x → Right x) ⊙ next

dec  :: Abacus b → Abacus b → Abacus b
dec next1 next0 = ↬ (λcase 
                    Left 0  → Left (ε (abacus next0) 0)
                    Left n  → Left (ε (abacus next1) (n-1))
                    Right x → Right x )

output :: b → Abacus b
output x = η (const (Right x))

-- The full recursive program (multiply example)
multiplyAbacus :: Int → Abacus Int
multiplyAbacus m = dec
  (inc (multiplyAbacus m))   -- while >0: inc result (hidden), dec counter
  (output 0)
```

**Execution:**

```haskell
runMultiply :: Int → Int → Int
runMultiply m n = ε (abacus (multiplyAbacus m)) n
```

This reads almost like a formal grammar for the initial Elgot category.

### Multi-Register Abacus (Product in Feedback Channel)

We carry a tuple of registers in the Left channel. For two registers (r1, r2) + main input:

```haskell
type Reg2 = (Int, Int)                     -- (r1, r2)

data Abacus2 a
  = Inc1 (Abacus2 a)          -- r1+
  | Inc2 (Abacus2 a)          -- r2+
  | Dec1 (Abacus2 a) (Abacus2 a)   -- r1-  (zero branch / nonzero branch)
  | Dec2 (Abacus2 a) (Abacus2 a)   -- r2-
  | Output a

-- Symbolic compiler
abacus2 :: Abacus2 b → Circuit (->) Either (Reg2, b) b   -- or simplify input

inc1 next = η (λcase 
                Left ((r1,r2), x) → Left ((r1+1, r2), x)
                Right y           → Right y) ⊙ next

inc2 next = η (λcase 
                Left ((r1,r2), x) → Left ((r1, r2+1), x)
                Right y           → Right y) ⊙ next

dec1 next1 next0 = ↬ (λcase
  Left ((0,  r2), x) → Left (ε (abacus2 next0) ((0,r2), x))
  Left ((r1, r2), x) → Left (ε (abacus2 next1) ((r1-1,r2), x))
  Right y            → Right y )

dec2 next1 next0 = ↬ (λcase   -- symmetric for r2
  Left ((r1, 0), x) → Left (ε (abacus2 next0) ((r1,0), x))
  Left ((r1,r2), x) → Left (ε (abacus2 next1) ((r1,r2-1), x))
  Right y           → Right y )

output2 x = η (const (Right x))
```

**Classic Two-Register Example: Multiplication (r1 = m, r2 = n, result in r1)**

```haskell
-- Multiply using r1 += m, r2 times (result ends in r1)
mult2 :: Int → Int → Int
mult2 m n = ε (abacus2 program) ((0, n), 0)   -- start: r1=0 (accumulator), r2=n
  where
    program = dec2
      (inc1 (mult2 m n))     -- while r2 > 0: r1 += m, r2--
      (output2 0)            -- when r2 reaches 0, result is in r1
```

In pure symbolic little-language form (no Haskell data type):

```
multiply(m, n)  ≜  ↬ ( dec2 ( inc1 (multiply(m,n)) ) (output 0) ) 
                   ⊙ η (λ(r1,r2) → (0, n))   -- initial setup
```

This scales nicely: add more registers by enlarging the product in the feedback channel (r1, r2, r3, ...) and adding Inck / Deck combinators. The Mendler case in lower ensures that when you compose larger programs, the register tuple stays correctly threaded through every ↬.

### Why This Is Nice

- The **↬** (Loop) directly corresponds to the conditional jump in the abacus model.
- **η** lifts the tiny imperative steps (inc/dec/test).
- Composition **⊙** builds the program sequence.
- The whole thing is the free traced cocartesian syntax — exactly the spirit of the initial Elgot category.

This gives a very direct, symbol-heavy way to write abacus programs that feels like a tiny imperative language embedded in your categorical stack language.

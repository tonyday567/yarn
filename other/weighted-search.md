# Weighted Search

Search strategies (DFS, BFS, weighted, etc.) as different **interpretations of the same Circuit structure**.

Inspired by Donnacha Kidney's "Algebras for Weighted Search" (ICFP 2021): different search orderings are just different ways of folding over the same polynomial structure.

## Design

A search space is a Circuit with:
- **Loop** for recursive branching
- **Either tensor** carrying weights (cost/priority)
- **Right** branch for success, **Left** for failure + weight

The same Circuit can be interpreted as DFS, BFS, or best-first by changing how we traverse the choice tree.

## Implementation

```haskell
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Examples.WeightedSearch where

import Circuit
import Data.List (sortOn)
import Prelude hiding (id, (.))

-- | A search space over a semiring w, producing results of type a.
type Search w a = Circuit (->) (Either w) () a

-- Basic combinators

-- | Succeed with a value (no branching).
success :: a -> Search w a
success a = Lift (const (Right a))

-- | Fail completely.
failure :: Search w a
failure = Lift (const (Left undefined))  -- weight undefined; ignored on dead branch

-- | Non-deterministic choice: try alternatives in sequence.
choose :: [a] -> Search w a
choose [] = failure
choose xs = Loop $ \case
  Right () -> Right (head xs)
  Left ()  -> choose (tail xs)

-- | Add a weight to the search path.
weight :: w -> Search w ()
weight w = Lift (const (Left w))

-- ============================================================
-- Interpreters: different orderings, same Circuit
-- ============================================================

-- | Depth-first search: collect all solutions and their cumulative weights.
dfs :: (Num w) => Search w a -> [(w, a)]
dfs s = go 0 s
  where
    go acc c =
      case run c () of
        Right a -> [(acc, a)]
        Left w  -> go (acc + w) c

-- | Breadth-first search: maintain a queue of (cost, continuation) pairs.
bfs :: (Num w, Eq w) => Search w a -> [(w, a)]
bfs s = bfs' [(0, s)]
  where
    bfs' [] = []
    bfs' ((acc, c):rest) =
      case run c () of
        Right a -> (acc, a) : bfs' rest
        Left w  -> bfs' (rest ++ [(acc + w, c)])

-- | Weighted/Dijkstra: sort by accumulated weight, always explore cheapest first.
weighted :: (Ord w, Num w) => Search w a -> [(w, a)]
weighted s = go [(0, s)]
  where
    go [] = []
    go queue =
      let ((acc, c):rest) = sortOn fst queue
      in case run c () of
           Right a -> (acc, a) : go rest
           Left w  -> go (sortOn fst (rest ++ [(acc + w, c)]))
```

## Example

```haskell
data Node = A | B | C | D deriving (Show, Eq)

pathsToC :: Search Int Node
pathsToC =
  (weight 1 >> success B) <|> (weight 3 >> success D) >>= \case
    B -> weight 2 >> success C
    D -> weight 1 >> success C
    _ -> failure

demo :: IO ()
demo = do
  putStrLn "=== Weighted Search Demo ==="
  putStrLn "Paths from A to C:"
  putStrLn $ "DFS:      " ++ show (dfs pathsToC)
  putStrLn $ "BFS:      " ++ show (bfs pathsToC)
  putStrLn $ "Weighted: " ++ show (weighted pathsToC)
```

## The Point

The **Circuit definition is search-agnostic**. It just says "here are my choices and costs." The **interpreter** decides the order:

- **DFS**: Greedy, depth-first recursion
- **BFS**: Queue-based level-order
- **Weighted**: Priority queue (Dijkstra)

All three run the exact same Circuit. This is the power of treating search as an algebraic structure: change the fold, change the strategy.

**Connection to Kidney's paper:** Kidney showed that search strategies form a monoidal algebra over a semiring. Our `Either w` tensor is exactly that semiring: choice (`Left`) + weight (`w`). Different interpreters are different monoidal folds over the same structure.

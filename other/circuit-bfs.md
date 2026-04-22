# Circuit: Breadth-First Search

A breadth-first search expressed as a Circuit feedback loop.

BFS requires threading state: a queue of nodes to visit, and a set of visited nodes. Circuit's `Loop` constructor is designed for exactly this pattern — the feedback tuple carries the state across iterations.

## Setup

We'll use a simple graph represented as an adjacency list and search for all nodes reachable from a starting node.

```haskell
{-# LANGUAGE RankNTypes #-}

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Control.Category (Category(..))
import Prelude hiding (id, (.))

-- Simple adjacency list graph
type Graph a = a -> [a]

-- State threaded through the loop:
-- Queue of nodes to visit + Set of already-visited nodes
type BFSState a = (Seq a, Set a)
```

## The Loop Function

The core of BFS is a function that takes `(state, node)` and produces `(state', discovered)`.

On each iteration:
- Input: next node from the queue
- Feedback: (queue of remaining nodes, visited set)
- Output: list of newly discovered nodes

```haskell
-- | Step function for BFS loop.
-- Takes (queue, visited) and a starting node.
-- Returns (queue', visited') and a list of nodes reached on this step.
bfsStep :: (Ord a, Show a) => Graph a -> ((Seq a, Set a), a) -> ((Seq a, Set a), [a])
bfsStep graph ((queue, visited), node) =
  if Set.member node visited
    then ((queue, visited), [])  -- Already visited, skip
    else
      let neighbors = graph node
          newVisited = Set.insert node visited
          unvisitedNeighbors = filter (not . flip Set.member newVisited) neighbors
          newQueue = queue Seq.>< Seq.fromList unvisitedNeighbors
      in ((newQueue, newVisited), node : unvisitedNeighbors)
```

## The Naive Run

Before we use Circuit, let's see the naive version to understand the structure:

```haskell
-- | Naive BFS: manually thread the loop until queue is empty.
bfsNaive :: (Ord a, Show a) => Graph a -> a -> [a]
bfsNaive graph start = go (Seq.singleton start, Set.empty)
  where
    go (queue, visited)
      | Seq.null queue = []
      | otherwise =
          let node = Seq.index queue 0
              rest = Seq.drop 1 queue
              ((queue', visited'), discovered) = bfsStep graph ((rest, visited), node)
          in discovered ++ go (queue', visited')
```

## Using Circuit's Loop

Now with Circuit — we express the loop structure explicitly:

```haskell
import Circuit (Circuit(..), Trace(..), run)

-- | BFS using Circuit's Loop.
-- The feedback carries (queue, visited).
-- On each iteration, we consume one node from the queue.
bfsCircuit :: (Ord a, Show a) => Graph a -> a -> [a]
bfsCircuit graph start = run circuit start
  where
    -- Circuit takes a starting node and runs the loop until queue is empty
    circuit :: Circuit (->) (,) a [a]
    circuit = Loop $ \((queue, visited), node) ->
      if Seq.null queue
        then ((queue, visited), [])
        else
          let nextNode = Seq.index queue 0
              rest = Seq.drop 1 queue
              ((queue', visited'), discovered) = bfsStep graph ((rest, visited), nextNode)
          in ((queue', visited'), discovered)
```

Wait—this doesn't quite work yet. The issue: `run` expects `Circuit a a -> a`, but we're trying to use BFS to accumulate a list. We need to rethink the type signature.

**Error 1:** What should the Circuit carry in the feedback? The queue+visited state, or something else?

Let me reconsider...

```haskell
-- | Alternative: the feedback IS the list we're building.
-- Each iteration adds to the discovered list.
bfsLoopAlt :: (Ord a, Show a) => Graph a -> ((Seq a, Set a, [a]), a) -> ((Seq a, Set a, [a]), [a])
bfsLoopAlt graph ((queue, visited, discovered), node) =
  if Set.member node visited
    then ((queue, visited, discovered), [])
    else
      let neighbors = graph node
          newVisited = Set.insert node visited
          unvisitedNeighbors = filter (not . flip Set.member newVisited) neighbors
          newQueue = queue Seq.>< Seq.fromList unvisitedNeighbors
          newDiscovered = discovered ++ [node]
      in ((newQueue, newVisited, newDiscovered), node : unvisitedNeighbors)
```

But then we still have the problem: how do we signal "done"?

## Let's step back

Actually, thinking about it: maybe the initial example should be simpler. Let's do a finite search (fixed depth or fixed number of steps) rather than "search until queue empty".

Or: we extract the result from the final state of the feedback tuple, not from the return value of `run`.

Let me restart with a clearer design...

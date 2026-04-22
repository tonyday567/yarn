# Circuit.Agent — Self-Updating Coinductive Agents

Concrete operational pattern: agents that update themselves based on their own history.

This is **Borges' Library reimagined**: an append-only log (Path) + a closure (Agent) that consumes the log and produces the next step, forever.

## Design

```haskell
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

module Circuit.Agent
  ( Path
  , Agent (..)
  , step
  , runAgent
  , forkAgent
  , compact
  ) where

import Circuit (Circuit (..), Trace (..))
import Hyp (Hyp (..), lift, invoke)
import Data.Text (Text)

-- | Path: the materialized history (append-only JSONL log prefix).
type Path = [Text]

-- | Agent: a self-updating closure.
--
-- Given current path, emit the next Text and the updated Agent.
-- Coinductive: the agent produces its own continuation.
newtype Agent = Agent
  { step :: Path -> (Text, Agent)
  }

-- | Run an agent from an initial path.
--
-- Produces an infinite stream of Text values.
-- The path grows monotonically as the agent updates.
runAgent :: Agent -> Path -> [Text]
runAgent a p =
  let (t, a') = step a p
  in t : runAgent a' (p ++ [t])

-- | Fork: literally identity on the current closure.
--
-- The Agent is already its own immutable closure.
-- Forking just returns the same function.
forkAgent :: Agent -> Agent
forkAgent = id

-- | Compact: reduce memory footprint via path compression.
--
-- Apply a function @f :: Path -> Path@ to compress the history
-- before passing it to the agent.
--
-- Example: keep only the last N steps, or a compressed summary.
compact :: (Path -> Path) -> Agent -> Agent
compact f a = Agent $ \p -> step a (f p)

-- | Optional embedding into Hyp.
--
-- Shows how Agent sits naturally on top of the Hyp machinery.
-- The continuation becomes the source of the current path.
agentToHyp :: Agent -> Hyp Path Text
agentToHyp (Agent s) = Hyp $ \k ->
  let (t, _a') = s (lower k [])   -- current path from continuation
  in t
```

## The Pattern

### Immutability and State

The Agent is **stateless in the traditional sense**: there's no mutable cell. Instead:

```haskell
step :: Path -> (Text, Agent)
```

The agent is a **function of its history**. The path is the state. The agent is the function that maps history → next step.

### Coinduction

`runAgent` is coinductive: it generates an infinite stream without forcing the entire computation upfront.

```haskell
runAgent :: Agent -> Path -> [Text]
runAgent a p = let (t, a') = step a p
               in t : runAgent a' (p ++ [t])
```

Each step:
1. Compute next text `t` from current path
2. Get updated agent `a'`
3. Append `t` to path
4. Continue with `a'` and the extended path

### Forking as Identity

`forkAgent = id` because the Agent is already a closure. There's no hidden state to share or isolate—the closure is the entire description of the agent.

If you want branching histories, you fork the Path, not the Agent:

```haskell
-- Two branches from the same agent
branch1 = runAgent a (p ++ ["choice1"])
branch2 = runAgent a (p ++ ["choice2"])
```

### Compaction

`compact f a` allows garbage collection of old history without losing the agent's ability to function.

Examples:
```haskell
-- Keep only last 100 steps
compactLast n = compact (takeEnd n)

-- Compress to a summary
compactSummary = compact summarizePath

-- Forget everything before a checkpoint
compactFrom checkpoint = compact (dropWhile (/= checkpoint))
```

The agent still functions correctly—it just doesn't see the discarded history.

## Example: A Simple Counter Agent

```haskell
counterAgent :: Agent
counterAgent = Agent $ \p ->
  let n = length p  -- count steps
  in (show n, counterAgent)

-- >>> take 5 $ runAgent counterAgent []
-- ["0", "1", "2", "3", "4"]
```

## Example: History-Dependent Agent

```haskell
-- | Agent that repeats the last output, or "start" if empty.
repeatAgent :: Agent
repeatAgent = Agent $ \p ->
  let last_output = case p of
                      [] -> "start"
                      (t:_) -> t
  in (last_output, repeatAgent)

-- >>> take 5 $ runAgent repeatAgent []
-- ["start", "start", "start", "start", "start"]
```

## Connection to Circuit and Hyp

- **Circuit**: syntax (free traced monoidal)
- **Hyp**: semantics (compact closed, fixed-point)
- **Back**: duality (bidirectional, reversible annotations)
- **Agent**: realization (coinductive self-updating closure)

Agent is what you get when you take Hyp's recursive semantics and **materialize it as an operational pattern**: the path is the unfolding of the recursion, the agent is the fixed-point function.

## Status

✓ Clean design, naturally captures the "self-updating log-based process" pattern.
⟝ Next: use Agent in larger examples (multi-agent systems, environment interaction, dialogue loops).

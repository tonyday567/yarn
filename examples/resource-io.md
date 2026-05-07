# Resource IO

Safe I/O and resource handling with `Circuit (Kleisli IO) Either`.

Three tiers of the same pattern built on `loopIO` — a convenience wrapper
that strips the Either feedback wrapper so step functions return
`IO (Either a b)` directly (`Left = continue`, `Right = done`).

```haskell
-- | Convenience wrapper: turns a step function directly into a Loop.
loopIO :: (a -> IO (Either a b)) -> Circuit (Kleisli IO) Either a b
loopIO step = Loop (Kleisli \case
  Right x -> step x
  Left  x -> step x)
```

The type `Circuit (Kleisli IO) Either a b` means: a state machine in IO
with state type `a` and exit type `b`. The `Either` tensor gives
sequential feedback — `Left` loops back, `Right` terminates.

## Tier 1 — Simplest loop (countdown)

A numeric loop with an IO effect. The `Right` exit path is the only way out.

```haskell
{-# LANGUAGE Arrows #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Control.Arrow (Kleisli (..), runKleisli)
import Circuit
import Circuit.Traced ()
import Prelude hiding (id, (.))

countdown :: Circuit (Kleisli IO) Either Int ()
countdown = loopIO \n ->
  if n <= 0
  then pure (Right ())                          -- exit
  else do
    putStrLn $ "tick " <> show n
    pure (Left (n - 1))                         -- loop with n-1

-- >>> runKleisli (run countdown) 3
-- tick 3
-- tick 2
-- tick 1
```

The feedback channel carries an `Int`. Each iteration either loops (`Left`)
or exits (`Right`). No resources, no interaction — just the bare mechanism.

## Tier 2 — Interactive loop (echo server)

Same structure, but now the state is `String` and the exit is triggered by
user input.

```haskell
echo :: Circuit (Kleisli IO) Either String ()
echo = loopIO \line ->
  if line `elem` ["quit", "exit", ":q"]
  then pure (Right ())                          -- exit
  else do
    putStrLn $ "echo: " <> line
    pure (Left "next>")                         -- feedback token

-- >>> runKleisli (run echo) "hello"
-- echo: hello
```

The feedback token `"next>"` is a prompt string, not actual user input.
For a true REPL you'd read from stdin in the loop body. The point here
is the pattern: `Left = continue with new state`, `Right = done`.

## Tier 3 — Resource lifecycle (file reader)

The canonical case. The feedback channel carries an open `Handle`.
The `Right` exit path is the single place where `hClose` is called —
guaranteeing cleanup without try/finally boilerplate.

```haskell
import System.IO (Handle, IOMode (..), hClose, hGetLine, hIsEOF, openFile)

-- | Read and print a file line by line, closing the handle on exit.
fileReader :: FilePath -> Circuit (Kleisli IO) Either Handle ()
fileReader path = loopIO \case
  () -> do                                      -- acquire
    h <- openFile path ReadMode
    pure (Left h)                               -- hand off to loop

  h -> do                                       -- use + decide
    eof <- hIsEOF h
    if eof
      then do
        hClose h                                -- release
        pure (Right ())                         -- exit
      else do
        line <- hGetLine h
        putStrLn line
        pure (Left h)                           -- continue with handle

-- >>> runKleisli (run (fileReader "examples/resource-file.md")) ()
```

The state machine phases:

```
  () → openFile → Left h ──┐
                            │
  ┌─────────────────────────┘
  │
  ▼
  h → hIsEOF? ─── yes → hClose h → Right ()
         │
         no → hGetLine → print → Left h ──┘
```

The handle lives on the feedback channel. The only way to exit is through
the branch that calls `hClose`. The type guarantees: you cannot reach
`Right ()` without releasing the resource, because `Right ()` is only
produced in the same branch as `hClose h`.

### Writing with acquire/use/release

Same pattern for write-mode files:

```haskell
fileWriter :: FilePath -> String -> Circuit (Kleisli IO) Either Handle ()
fileWriter path content = loopIO \case
  () -> do                                      -- acquire
    h <- openFile path WriteMode
    pure (Left h)

  h -> do                                       -- use + release
    hPutStrLn h content
    hClose h
    pure (Right ())
```

## Pattern

All three share the same type and mechanism:

| tier         | state type | exit trigger       | resource? |
|-------------|-----------|--------------------|-----------|
| countdown    | `Int`     | `n <= 0`           | none      |
| echo         | `String`  | `"quit"` in input  | none      |
| file reader  | `Handle`  | EOF reached        | yes       |

The key guarantee: **the `Right` exit path is the single place where cleanup
happens**. For file handles this means `hClose` is always called. For
sockets, databases, or any other resource, the same structure applies:
acquire on first call, carry the resource through `Left` feedback, release
before returning `Right`.

The `Either` tensor enforces the structure:
- `Left` = feedback, the loop continues with new state
- `Right` = terminal, the loop exits

There is no "fall through" or "exception escape" — the type system
guarantees every path through the loop body returns either `Left` or `Right`,
and only `Right` terminates. If you need to release a resource, you must do
it before returning `Right`.

Compare with `whileK` from `Circuit.Traced`, which uses the inverted
convention (`Left = done`, `Right = continue`) matching the Hyper/while
style. `loopIO` uses the Trace-native convention (`Left = feedback`,
`Right = exit`). Both are valid; `loopIO` is simpler for most I/O patterns.

## Mechanism

Under the hood, `loopIO` creates a `Loop (Kleisli body)` which is executed
by the `Trace (Kleisli IO) Either` instance using GHC's delimited
continuation primops (`prompt` / `control0`). This gives constant stack
usage — the loop body is re-entered at the `prompt` boundary every iteration,
never building up a call stack.

See `examples/circuits-delim.md` for the theory correspondence:
```
Trace (Kleisli IO) Either   ≅   delimited continuations
Loop                        ≅   reset / prompt
feedback Left               ≅   shift / control0
exit Right                  ≅   return from reset
```

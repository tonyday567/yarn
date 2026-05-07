# Circuit Parsing

Parser combinators on Circuit. A parser is `s -> Maybe (a, s)` — consume
input, produce a result with remaining input, or fail. Circuit constructs
provide the control flow: `Lift` for primitives, `Loop` for repetition,
`Compose` for sequencing, and the `Either` tensor for choice/backtracking.

## Parser type

```haskell
{-# LANGUAGE DerivingVia #-}

newtype Parser s a = Parser { unParser :: Circuit (->) (,) s (Maybe (a, s)) }

-- | Run a parser.
parse :: Parser s a -> s -> Maybe (a, s)
parse = reify . unParser
```

The `(,)` tensor threads input state. For rapid development, derive the
standard instances via `StateT s Maybe` — the isomorphism `s -> Maybe (a, s) ≅
StateT s Maybe a` gives us `Functor`, `Applicative`, `Alternative`, `Monad`,
`MonadPlus` for free. Circuit provides the *implementation*; `StateT`
provides the *interface*.

```haskell
newtype Parser s a = Parser { runParser :: s -> Maybe (a, s) }
  deriving (Functor, Applicative, Alternative, Monad, MonadPlus)
    via StateT s Maybe
```

Dual accessors: `runParser` for the derived instances, `unParser` for
Circuit inspection.

## Primitives via Lift

`Lift` embeds a function. For character-level parsing:

```haskell
import Data.Char (isDigit, digitToInt)

satisfy :: (Char -> Bool) -> Parser String Char
satisfy p = Parser $ Lift $ \case
  (c:cs) | p c -> Just (c, cs)
  _             -> Nothing

char :: Char -> Parser String Char
char = satisfy . (==)

digit :: Parser String Int
digit = Parser $ Lift $ \case
  (c:cs) | isDigit c -> Just (digitToInt c, cs)
  _                   -> Nothing
```

## Repetition via Loop

The `(,)` tensor's `Loop` carries state through a lazy feedback knot.
The body receives `(feedback_state, input)` and returns
`(new_feedback_state, output)`.

For `manyDigits` — read digits, accumulate as an Int:

```haskell
-- | Parse consecutive digits into an Int. Uses Loop over (,) tensor.
-- The feedback channel carries (remaining_input, accumulated_value).
manyDigits :: Circuit (->) (,) (String, Int) Int
manyDigits = Loop $ \((s, n), ()) ->
  case s of
    (c:cs) | isDigit c -> ((cs, n * 10 + digitToInt c), ())   -- loop
    _                   -> ((s, n), n)                          -- exit
```

Trace for input `"123abc"`:

```
(((),0), ()) → '1' digit → (("23abc", 1), ())
(("23abc", 1), ()) → '2' digit → (("3abc", 12), ())
(("3abc", 12), ()) → '3' digit → (("abc", 123), ())
(("abc", 123), ()) → 'a' not digit → (("abc", 123), 123)  -- exit
```

`reify manyDigits ("123abc", 0)` gives `123`.

For `many` (zero or more, accumulating a list):

```haskell
many :: Parser String a -> Circuit (->) (,) (String, [a]) [a]
many (Parser p) = Loop $ \((s, as), ()) ->
  case reify p s of
    Just (a, s') -> ((s', a : as), ())    -- success: loop with new state
    Nothing       -> ((s, as), as)         -- failure: exit with accumulated
```

This maps to `(,)` tensor nicely: the feedback pair is
`(remaining_input, reversed_results)`, the output is the result list
(reversed back by the caller).

## Choice via Either tensor

`<|>` is where the `Either` tensor is genuine alternation — not the
degenerate `either step step` pattern from I/O loops. Try `p1`; if it
fails, try `p2`.

```haskell
(<|>) :: Parser s a -> Parser s a -> Parser s a
Parser p1 <|> Parser p2 = Parser $ Lift (trace body)
  where
    body :: Either s s -> Either s (Maybe (a, s))
    body (Right s) =                          -- first phase: try p1
      case reify p1 s of
        Just r  -> Right (Just r)             -- success → exit
        Nothing -> Left s                     -- failure → loop
    body (Left s) =                           -- second phase: try p2
      case reify p2 s of
        Just r  -> Right (Just r)             -- success → exit
        Nothing -> Right Nothing              -- failure → exit
```

The `trace` from `Trace (->) Either` collapses `Either s s → Either s (Maybe
(a, s))` to `s → Maybe (a, s)`. `Lift` re-embeds it into the `(,)`-tensor
Circuit. The `Either` tensor is used internally and erased — the outer
parser type stays `(,)`-tensor for composition.

The two phases correspond to the two branches of `|` in regex:

```
Right s  →  try p1(s)  →  success: exit  |  failure: Left s
Left s   →  try p2(s)  →  success: exit  |  failure: exit Nothing
```

## Iconic example: digits

Using the derived `Alternative` instance:

```haskell
-- | Parse one or more digits as an Int.
-- >>> parse digits "123abc"
-- Just (123, "abc")
-- >>> parse digits "no digits"
-- Nothing
digits :: Parser String Int
digits = read <$> some (satisfy isDigit)

-- | Parse two digit groups separated by 'x'.
-- >>> parse digitPair "12x34rest"
-- Just ((12, 34), "rest")
digitPair :: Parser String (Int, Int)
digitPair = (,) <$> (digits <* char 'x') <*> digits

-- | Parse a digit optionally followed by another.
-- >>> parse digitOptional "1abc"
-- Just ([1], "abc")
-- >>> parse digitOptional "12abc"
-- Just ([1, 2], "abc")
digitOptional :: Parser String [Int]
digitOptional = some digit <|> (pure <$> digit)
```

## Regex connection

The mapping from regex operators to Circuit constructs:

| regex         | parser combinator          | Circuit construct           |
|--------------|---------------------------|----------------------------|
| `[0-9]`      | `satisfy isDigit`         | `Lift`                     |
| `[0-9]+`     | `some (satisfy isDigit)`  | `Loop` over `(,)` tensor   |
| `a\|b`       | `p1 <\|> p2`              | `Either` tensor + `trace`  |
| `ab`         | `p1 *> p2`                | `Compose`                  |
| `a*`         | `many p`                  | `Loop` over `(,)` tensor   |
| `a?`         | `p <\|> pure mempty`      | `Either` tensor            |

## These: the progress-aware tensor

`Maybe (a, s)` conflates two distinct failures:

```
Nothing  =  "didn't consume, try alternative"   -- recoverable
            "catastrophic error"                 -- unrecoverable
```

huihua's `Result e a = OK a s | Fail | Err e` splits this into three
outcomes. `These` captures the same distinction at the type level:

| these case     | parsing meaning                    | `<|>` behaviour     |
|---------------|------------------------------------|---------------------|
| `These a s`   | consumed, have result + remainder  | success, stop       |
| `That s`      | no progress, input untouched       | try next alternative|
| `This a`      | consumed everything, final result  | success, EOF        |

`That s` is the missing case in `Maybe` — the signal that says "I touched
nothing, backtrack to the next branch." With `Maybe`, `<|>` can't
distinguish "failed without consuming" from "failed after consuming, can't
backtrack." `These` makes this structural.

The full parser type with error channel:

```haskell
type Parser e s a = Circuit (->) (,) s (Either e (These a s))
```

But `These` itself can serve as a tensor — `That` for feedback, `This` for
exit, `These` for exit-with-remainder:

```haskell
type Parser s a = Circuit (->) These s a
```

A `Trace arr These` instance would handle the three-way control flow
natively — `That s` loops, `This a` exits with result, `These a s` exits
with result + leftover state. This unifies repetition and choice into one
tensor.

## Territory coverage

Can Circuit-parser cover the existing parser libraries in `~/haskell/`?

| library        | approach                  | Circuit encoding                                  |
|---------------|--------------------------|---------------------------------------------------|
| `mtok`        | regex-applicative `RE s a`| `Circuit (->) Either s [a]`, `<|>` maps directly  |
| `huihua`      | `Parser e a`, `Result e a`| `Circuit (->) These s (Either e a)`               |
| `dotparse`    | FlatParse.Basic + TH      | same as huihua + TH for literals                  |
| `markup-parse`| tokenize → gather pipeline| Circuit tokenizer feeds Circuit tree builder      |

`mtok` is the easiest win — it already uses `regex-applicative` whose `(<|>)`
is the same `Either`-tensor pattern. Replace `RE Char a` with
`Circuit (->) Either String [a]` and `foldr1 (<|>)` maps to `Loop`-level
choice.

`huihua`'s `Result e a` maps to `These` — the three outcomes are exactly
the three `These` constructors plus an error channel. The `Parser e a`
newtype becomes `Circuit (->) These ByteString (Either e a)`.

`dotparse` uses FlatParse.Basic which is the same shape as huihua (huihua
was designed as a drop-in replacement). The TH quasi-quoter `$(char '.')`
compiles to checked string literals; the same technique works with Circuit.

`markup-parse` is a two-pass architecture: `tokenize` → `gather`. Each
pass is a Circuit: the tokenizer is a `Loop` over characters, the tree
builder is a `Loop` over tokens. The composition is `Compose`.

## Tensor summary

| tensor   | use in parsers            | semantic                      |
|---------|--------------------------|-------------------------------|
| `(,)`   | state threading, `many`   | deterministic, lazy knot      |
| `Either`| `<|>`, backtracking     | nondeterministic, alternation |
| `These` | progress-aware `<|>`      | That=retry, These=success     |

The `Either` tensor carries genuine computational alternatives — two
distinct parsers tried in order. This is the real use of `Either` as a
tensor, distinct from the degenerate `either step step` where both
branches call the same function (i.e., `Either a a ≅ (Bool, a)`).

`These` takes this further: where `Either` conflates failure modes,
`These` separates "no progress" from "catastrophic error" at the type
level, making backtracking semantics structural rather than convention.

## What's next

- `Trace arr These` instance — the three-way control flow operator
- `choice :: [Parser s a] -> Parser s a` — generalised `<|>` via list-indexed
  feedback
- `mtok` refactor: replace `regex-applicative` with Circuit
- `huihua` refactor: `Parser e a` as `Circuit (->) These ByteString (Either e a)`
- JSON parser as a full backtracking example

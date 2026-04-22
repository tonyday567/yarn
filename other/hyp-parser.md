# Hyp Parser Combinators

Parsers built directly using `Hyp`, the final encoding of circuits.

This shows the **algebraic / coinductive** view: parsers as recursive hyperfunctions that thread input state through a sequence of reductions.

## Design

A `Parser a` is just a `Hyp String (Either String a)` — a hyperfunction that takes input and produces either a failure message or a result. The fixed-point structure of Hyp naturally expresses repetition (many, some) and choice (Alternative).

## Implementation

```haskell
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Examples.HypParser where

import Hyp
import Data.Char (isDigit, digitToInt)
import Prelude hiding (id, (.))

-- | A parser is a Hyp that consumes a String and produces a result (or fails).
type Parser a = Hyp String (Either String a)

-- | Core primitive: try a predicate on the next character.
satisfy :: (Char -> Bool) -> Parser Char
satisfy p = lift $ \input ->
  case input of
    (c:cs) | p c   -> Right (cs, c)
    _              -> Left "satisfy failed"

-- | Parse a specific character.
char :: Char -> Parser Char
char c = satisfy (== c)

-- | Parse zero or more occurrences (fixed-point recursion in Hyp).
many :: Parser a -> Parser [a]
many p = fix $ \rec ->
  (do x  <- p
      xs <- rec
      pure (x:xs))
  <|> pure []

-- | Parse one or more occurrences.
some :: Parser a -> Parser [a]
some p = (:) <$> p <*> many p

-- | Choice: left-biased, uses Hyp's MonadPlus instance.
(<|>) :: Parser a -> Parser a -> Parser a
p <|> q = lift $ \input ->
  case lower p input of
    Right (rest, x) -> Right (rest, x)
    Left _          -> lower q input

-- Examples

-- | Parse a single digit.
digit :: Parser Int
digit = digitToInt <$> satisfy isDigit

-- | Parse a multi-digit number.
number :: Parser Int
number = do
  ds <- some digit
  pure (foldl (\n d -> n*10 + d) 0 ds)

-- | Run a parser on input.
parse :: Parser a -> String -> Either String (String, a)
parse p input = lower p input
```

## Example Usage

```haskell
-- >>> parse number "12345abc"
-- Right ("abc", 12345)

-- >>> parse number "xyz"
-- Left "satisfy failed"

-- >>> parse (many digit) "42"
-- Right ("", [4, 2])
```

## Comparison

| Approach | Style | Stack | Semantics |
|----------|-------|-------|-----------|
| **Circuit (->)** | Initial (GADT) | Lazy knot-tying | Pure state threading |
| **Hyp** | Final (Recursive) | Coinductive fixed-point | Algebraic, fixed-point closed |
| **Circuit (Kleisli IO)** | Initial (GADT) | Delimited continuations | Efficient, supports effects |

Hyp is the most natural for **reasoning** about parsers: it's just recursion and algebraic laws. Circuit is more general for **implementation** (you can use any arrow). The final Hyp encoding is the "truth model" — other encodings are optimizations or alternative implementations.

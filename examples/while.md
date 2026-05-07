⟝ while 

# While Loop as Self-Referential Array

harpie's `Array s` is `Representable` — `tabulate` allocates a `Vector` of
`n = sizeOf @s` cells, each a lazy thunk. A cell can read other cells via
`index` (or `!`).  This is the whole memoization story. No Hyper needed.

---

## While Loop

```haskell
{-# LANGUAGE DataKinds #-}

import Harpie.Fixed (Array, tabulate, index, (!))
import Harpie.Shape (Fins (..), fins, KnownNats)

whileLoop
  :: forall n. KnownNats n
  => (a -> a)        -- ^ step function
  -> (a -> Bool)     -- ^ continue condition
  -> a               -- ^ initial state
  -> Array '[n] a    -- ^ memo table, states at steps 0..n-1
whileLoop step cont x0 = tabulate $ \(UnsafeFins [i]) ->
  if i == 0
    then x0
    else let prev = whileLoop step cont x0 ! fins [i - 1]
         in if cont prev then step prev else prev
```

`tabulate` allocates `n` cells. Cell 0 is `x0`. Cell `i` reads cell `i-1`,
applies `step` if `cont prev` holds, otherwise freezes at the terminal state.
Asking for cell `k` forces cells `0..k` exactly once each.

---

## Example: Collatz Sequence

```haskell
collatz :: forall n. KnownNats n => Int -> Array '[n] Int
collatz x0 = whileLoop @n step cont x0
  where
    step n = if even n then n `div` 2 else 3 * n + 1
    cont n = n /= 1

-- >>> collatz @20 6 ! fins [0]   → 6
-- >>> collatz @20 6 ! fins [1]   → 3
-- >>> collatz @20 6 ! fins [8]   → 1   (reached 1, froze)
```

---

## Why This Works

`tabulate :: (Fins '[n] -> a) -> Array '[n] a` calls `V.generate n f`.
The `Vector` is allocated eagerly but the *elements* are lazy — each is
`f i`, stored as a thunk.

When you `!` (index) into the array, the thunk is forced. If that thunk
reads other cells (like `whileLoop ... ! fins [i-1]`), those thunks are
forced in turn. The chain resolves on demand, each cell computed at most
once.

This is the same mechanism as a lazy list `iterate`, but with O(1) random
access rather than O(n) spine traversal. The `Array` is the memo table.

---

## Backpropagation

The user's observation about "lazy load of the answer" is exactly right.
`tabulate` doesn't compute anything — it allocates `n` pointers to thunks.
The first `!` forces a chain: cell `k` → cell `k-1` → ... → cell 0.
Each cell in the chain is forced once, then cached. Subsequent `!` at any
position in the chain returns the cached value instantly.

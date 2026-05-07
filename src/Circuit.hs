{-# LANGUAGE RankNTypes #-}

-- | Circuit: free traced monoidal categories and hyperfunctions.
--
-- The main entry point. For most use cases, import submodules directly:
--
-- > import Circuit.Circuit (Circuit (..), reify)
-- > import Circuit.Hyper (Hyper (..), run, lower)
-- > import Circuit.Traced (Trace (..))
--
-- For detailed design and theory, see @other\/narrative-arc.md@ and @other\/axioms-hyp.md@.
--
-- For proofs by example (Agent, Dual, Parser patterns, and more), see @examples/@.

module Circuit
  ( -- * Circuit (initial encoding)
    Circuit (..),
    reify,
    lower,
    push,
    toHyper,
    hyperfy,

    -- * Hyper (final encoding)
    Hyper (..),
    type (↬),
    run,
    base,
    lift,
    hyperAp,
    hyperBind,
    valueFix,
    hyperFix,

    -- * Coinductive helpers
    unroll,
    roll,
    ana,
    cata,

    -- * Symbolic operators
    (⇸),
    (⊙),
    (⊲),
    (↬),
    (⥀),
    (↯),
    (⥁),
    (○),
    (↑),
    (↓),

    -- * Trace typeclass
    Trace (..),
    PromptTag,
    newPromptTag,
    prompt,
    control0,
    whileK,
  )
where

import Circuit.Circuit
  ( Circuit (..),
    reify,
    lower,
    push,
    toHyper,
    hyperfy,
    (⊙),
    (⊲),
    (↬),
    (↑),
    (↓),
    (⥀),
    (↯),
  )
import Circuit.Hyper
  ( Hyper (..),
    type (↬),
    run,
    base,
    lift,
    hyperAp,
    hyperBind,
    valueFix,
    hyperFix,
    unroll,
    roll,
    ana,
    cata,
    (⇸),
    (⥁),
    (○),
  )
import Circuit.Traced
  ( Trace (..),
    PromptTag,
    newPromptTag,
    prompt,
    control0,
    whileK,
  )

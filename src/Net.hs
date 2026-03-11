{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Net where

import Control.Category (Category (..))
import Harpie.Array qualified as A
import LensS (LensS (..), Store (..), getS, mkLensS, setS)
import Para (Para (..), runPara)
import Traced (Traced (..), run)
import Prelude hiding (id, (.))

-- ---------------------------------------------------------------------------
-- Parameter record
-- ---------------------------------------------------------------------------

data NetParams a = NetParams
  { w1 :: A.Array a,
    b1 :: A.Array a,
    w2 :: A.Array a,
    b2 :: A.Array a
  }

-- ---------------------------------------------------------------------------
-- Layer lenses into NetParams
-- ---------------------------------------------------------------------------

lensW1 :: LensS (NetParams a) (A.Array a)
lensW1 = mkLensS w1 (\p w -> p {w1 = w})

lensB1 :: LensS (NetParams a) (A.Array a)
lensB1 = mkLensS b1 (\p b -> p {b1 = b})

lensW2 :: LensS (NetParams a) (A.Array a)
lensW2 = mkLensS w2 (\p w -> p {w2 = w})

lensB2 :: LensS (NetParams a) (A.Array a)
lensB2 = mkLensS b2 (\p b -> p {b2 = b})

-- ---------------------------------------------------------------------------
-- Forward pass layers
-- ---------------------------------------------------------------------------

linear1 :: (Num a) => Traced (Para (NetParams a)) (A.Array a) (A.Array a)
linear1 = Lift $ Para $ \(p, x) -> A.mult (w1 p) x

bias1 :: (Num a) => Traced (Para (NetParams a)) (A.Array a) (A.Array a)
bias1 = Lift $ Para $ \(p, x) -> x + b1 p

relu1 :: (Ord a, Num a) => Traced (Para (NetParams a)) (A.Array a) (A.Array a)
relu1 = Lift $ Para $ \(_, x) -> fmap (max 0) x

linear2 :: (Num a) => Traced (Para (NetParams a)) (A.Array a) (A.Array a)
linear2 = Lift $ Para $ \(p, x) -> A.mult (w2 p) x

bias2 :: (Num a) => Traced (Para (NetParams a)) (A.Array a) (A.Array a)
bias2 = Lift $ Para $ \(p, x) -> x + b2 p

model :: (Num a, Ord a) => Traced (Para (NetParams a)) (A.Array a) (A.Array a)
model = bias2 . linear2 . relu1 . bias1 . linear1

forward :: (Num a, Ord a) => NetParams a -> A.Array a -> A.Array a
forward p x = runPara (run model) p x

-- ---------------------------------------------------------------------------
-- Backward pass layers
-- ---------------------------------------------------------------------------

linear1B ::
  (Num a, Fractional a) =>
  Traced (Para (NetParams a)) (A.Array a) (Store (A.Array a) (A.Array a))
linear1B = Lift $ Para $ \(p, x) ->
  Store
    (\dy -> A.mult (A.transpose (w1 p)) dy)
    (A.mult (w1 p) x)

bias1B ::
  (Num a) =>
  Traced (Para (NetParams a)) (A.Array a) (Store (A.Array a) (A.Array a))
bias1B = Lift $ Para $ \(p, x) ->
  Store id (x + b1 p)

relu1B ::
  (Ord a, Num a) =>
  Traced (Para (NetParams a)) (A.Array a) (Store (A.Array a) (A.Array a))
relu1B = Lift $ Para $ \(_, x) ->
  Store
    (\dy -> A.zipWith (\xi dyi -> if xi > 0 then dyi else 0) x dy)
    (fmap (max 0) x)

-- ---------------------------------------------------------------------------
-- Store composition
-- ---------------------------------------------------------------------------

andThen ::
  Para p a (Store b a) ->
  Para p b (Store c b) ->
  Para p a (Store c a)
andThen f g = Para $ \(p, a) ->
  case unPara f (p, a) of
    Store bwd_a b ->
      case unPara g (p, b) of
        Store bwd_b c ->
          Store (bwd_a . bwd_b) c

modelB ::
  (Ord a, Num a, Fractional a) =>
  Para (NetParams a) (A.Array a) (Store (A.Array a) (A.Array a))
modelB = run linear1B `andThen` run bias1B `andThen` run relu1B

-- ---------------------------------------------------------------------------
-- Test
-- ---------------------------------------------------------------------------

runModelB ::
  (Ord a, Num a, Fractional a) =>
  NetParams a -> A.Array a -> (A.Array a, A.Array a)
runModelB p x =
  case unPara modelB (p, x) of
    Store bwd y -> (y, bwd y)

-- ---------------------------------------------------------------------------
-- Weight gradients and parameter updates
-- ---------------------------------------------------------------------------
--
-- The Store backward pass gives input gradients.
-- Weight gradients need the saved input x — captured in the closure.
--
-- For linear y = W x:
--   dL/dW = dL/dy ⊗ x    (outer product)
--   dL/db = dL/dy         (bias gradient = upstream gradient)
--
-- We extend Store to carry param update alongside input gradient.

-- | Backward pass returning (input gradient, param update fn).
-- The param update fn takes upstream gradient and learning rate.
data BackPass b a s p = BackPass
  { inputGrad :: b -> a,
    paramUpdate :: b -> s -> p -> p
  }

linear1BP ::
  (Num a, Fractional a) =>
  Traced
    (Para (NetParams a))
    (A.Array a)
    (Store (A.Array a) (BackPass (A.Array a) (A.Array a) a (NetParams a)))
linear1BP = Lift $ Para $ \(p, x) ->
  Store
    ( \dy ->
        BackPass
          (\dy' -> A.mult (A.transpose (w1 p)) dy')
          ( \dy' lr params ->
              params
                { w1 = w1 params - fmap (lr *) (A.expand (*) dy' x),
                  b1 = b1 params - fmap (lr *) dy'
                }
          )
    )
    (A.mult (w1 p) x)

-- | MSE loss: L = (1/n) sum (y - y')^2
-- Returns (loss value, gradient dL/dy)
mseLoss ::
  (Num a, Fractional a) =>
  A.Array a -> A.Array a -> (a, A.Array a)
mseLoss y target =
  let diff = y - target
      n = fromIntegral (A.size y)
      loss = sum (fmap (^ 2) diff) / n
      grad = fmap (* (2 / n)) diff
   in (loss, grad)

step ::
  (Ord a, Num a, Fractional a) =>
  a -> NetParams a -> A.Array a -> A.Array a -> (a, NetParams a)
step lr p x target =
  let y = forward p x
      (loss, dOut) = mseLoss y target
      Store mkBP _ = unPara (run linear1BP) (p, x)
      bp = mkBP dOut
      p' = paramUpdate bp dOut lr p
   in (loss, p')

-- ---------------------------------------------------------------------------
-- Remaining backward layers
-- ---------------------------------------------------------------------------

bias1BP ::
  (Num a) =>
  Traced
    (Para (NetParams a))
    (A.Array a)
    (Store (A.Array a) (BackPass (A.Array a) (A.Array a) a (NetParams a)))
bias1BP = Lift $ Para $ \(p, x) ->
  Store
    ( \dy ->
        BackPass
          id -- gradient passes through
          ( \dy' lr params ->
              params
                { b1 = b1 params - fmap (lr *) dy'
                }
          )
    )
    (x + b1 p)

relu1BP ::
  (Ord a, Num a) =>
  Traced
    (Para (NetParams a))
    (A.Array a)
    (Store (A.Array a) (BackPass (A.Array a) (A.Array a) a (NetParams a)))
relu1BP = Lift $ Para $ \(_, x) ->
  Store
    ( \dy ->
        BackPass
          (\dy' -> A.zipWith (\xi dyi -> if xi > 0 then dyi else 0) x dy')
          (\_ _ params -> params) -- no parameters to update
    )
    (fmap (max 0) x)

linear2BP ::
  (Num a, Fractional a) =>
  Traced
    (Para (NetParams a))
    (A.Array a)
    (Store (A.Array a) (BackPass (A.Array a) (A.Array a) a (NetParams a)))
linear2BP = Lift $ Para $ \(p, x) ->
  Store
    ( \dy ->
        BackPass
          (\dy' -> A.mult (A.transpose (w2 p)) dy')
          ( \dy' lr params ->
              params
                { w2 = w2 params - fmap (lr *) (A.expand (*) dy' x),
                  b2 = b2 params - fmap (lr *) dy'
                }
          )
    )
    (A.mult (w2 p) x)

bias2BP ::
  (Num a) =>
  Traced
    (Para (NetParams a))
    (A.Array a)
    (Store (A.Array a) (BackPass (A.Array a) (A.Array a) a (NetParams a)))
bias2BP = Lift $ Para $ \(p, x) ->
  Store
    ( \dy ->
        BackPass
          id
          ( \dy' lr params ->
              params
                { b2 = b2 params - fmap (lr *) dy'
                }
          )
    )
    (x + b2 p)

-- ---------------------------------------------------------------------------
-- BackPass andThen — chains input gradients and composes param updates
-- ---------------------------------------------------------------------------

andThenBP ::
  Para p a (Store b (BackPass b a s p)) ->
  Para p b (Store c (BackPass c b s p)) ->
  Para p a (Store c (BackPass c a s p))
andThenBP f g = Para $ \(p, a) ->
  case unPara f (p, a) of
    Store mkBP_a b ->
      case unPara g (p, b) of
        Store mkBP_b c ->
          Store
            ( \dc ->
                let bp_b = mkBP_b dc
                    bp_a = mkBP_a (inputGrad bp_b dc)
                 in BackPass
                      -- chain input gradients: c -> b -> a
                      (\dc' -> inputGrad bp_a (inputGrad bp_b dc'))
                      -- compose param updates: apply both
                      ( \dc' lr params ->
                          paramUpdate
                            bp_a
                            (inputGrad bp_b dc')
                            lr
                            (paramUpdate bp_b dc' lr params)
                      )
            )
            c

-- ---------------------------------------------------------------------------
-- Full model with backward pass
-- ---------------------------------------------------------------------------

modelBP ::
  (Ord a, Num a, Fractional a) =>
  Para
    (NetParams a)
    (A.Array a)
    (Store (A.Array a) (BackPass (A.Array a) (A.Array a) a (NetParams a)))
modelBP =
  run linear1BP
    `andThenBP` run bias1BP
    `andThenBP` run relu1BP
    `andThenBP` run linear2BP
    `andThenBP` run bias2BP

-- ---------------------------------------------------------------------------
-- Full training step
-- ---------------------------------------------------------------------------

stepFull ::
  (Ord a, Num a, Fractional a) =>
  a -> NetParams a -> A.Array a -> A.Array a -> (a, NetParams a)
stepFull lr p x target =
  let Store mkBP y = unPara modelBP (p, x)
      (loss, dOut) = mseLoss y target
      bp = mkBP dOut
      p' = paramUpdate bp dOut lr p
   in (loss, p')

{-
p = NetParams (A.ident [3,3]) (A.konst [3] 0) (A.ident [3,3]) (A.konst [3] 0)
x = A.array [3] [1.0, -2.0, 3.0]
target = A.array [3] [1.0, 0.0, 1.0]
stepFull 0.01 p x target
losses = fst $ foldl (\(ls,p) _ -> let (l,p') = stepFull 0.01 p x target in (ls++[l],p')) ([],p) [1..20]
losses
-}

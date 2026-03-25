{-# LANGUAGE GADTs #-}

module SysL
  ( Ty (..)
  , Val (..)
  , Result (..)
  , Command (..)
  , Value (..)
  , Term (..)
  , Coterm (..)
  , Env
  , Output
  , evalCommand
  , evalValue
  , evalTerm
  , evalCoterm
    -- * Helpers
  , lookupEnv
    -- * Tests
  , testId
  , testThen
  ) where

-- | Types
data Ty
  = One
  | Times Ty Ty
  | Zero
  | Plus Ty Ty
  | Hom Ty Ty
  | GradedHom Ty [Ty]
  | Then Ty Ty
  deriving (Show, Eq)

-- | Runtime result: which output slot fired and with what value
data Result v = RVal Int (Val v)
  deriving (Show)

-- | Values, parametric in domain type v
data Val v
  = VUnit
  | VPair (Val v) (Val v)
  | VLeft (Val v)
  | VRight (Val v)
  | VFun (Val v -> Result v)
  | VGradedFun (Val v -> Result v)
  | VThen (Val v) (Val v -> Result v)  -- Fw a, Bw a x -> Fw b
  | VEmbed v                            -- opaque domain value

instance Show v => Show (Val v) where
  show VUnit          = "VUnit"
  show (VPair a b)    = "VPair (" <> show a <> ") (" <> show b <> ")"
  show (VLeft a)      = "VLeft (" <> show a <> ")"
  show (VRight b)     = "VRight (" <> show b <> ")"
  show (VFun _)       = "VFun <fn>"
  show (VGradedFun _) = "VGradedFun <fn>"
  show (VThen a _)    = "VThen (" <> show a <> ") <fn>"
  show (VEmbed v)     = "VEmbed (" <> show v <> ")"

-- | Input environment: de Bruijn indexed list of values
type Env v = [Val v]

-- | Output: which slot fired, what value
type Output v = (Int, Val v)

lookupEnv :: Int -> Env v -> Val v
lookupEnv 0 (x : _)  = x
lookupEnv n (_ : xs) = lookupEnv (n - 1) xs
lookupEnv _ []        = error "lookupEnv: index out of range"

-- | Syntax
data Command v
  = Cut (Term v) (Coterm v)
  deriving (Show)

data Value v
  = Var Int
  | TensorIntro (Value v) (Value v)
  | PlusIntroL (Value v)
  | PlusIntroR (Value v)
  | HomComatch (Command v)
  | GradedHomComatch (Command v)
  | Lit (Val v)                  -- inject a Val directly
  deriving (Show)

data Term v
  = Embed (Value v)
  | Mu (Command v)
  | ThenComatch (Command v)      -- cmd with a::b::bs, focuses Then a b
  deriving (Show)

data Coterm v
  = Covar Int
  | Comu (Command v)
  | TensorMatch (Command v)
  | PlusMatch (Command v) (Command v)
  | HomCointro (Term v) (Coterm v)
  | GradedHomCointro (Term v) [Coterm v]
  | ThenCointro (Coterm v) (Coterm v)  -- sequential split
  deriving (Show)

-- | Evaluator

evalCommand :: Command v -> Env v -> Output v
evalCommand (Cut t k) env =
  case evalTerm t env of
    Left out  -> out
    Right val -> evalCoterm k env val

evalValue :: Value v -> Env v -> Val v
evalValue (Var i) env              = lookupEnv i env
evalValue (TensorIntro v1 v2) env  = VPair (evalValue v1 env) (evalValue v2 env)
evalValue (PlusIntroL v) env       = VLeft (evalValue v env)
evalValue (PlusIntroR v) env       = VRight (evalValue v env)
evalValue (HomComatch cmd) env     =
  VFun $ \x ->
    let (slot, val) = evalCommand cmd (x : env)
    in RVal slot val
evalValue (GradedHomComatch cmd) env =
  VGradedFun $ \x ->
    let (slot, val) = evalCommand cmd (x : env)
    in RVal slot val
evalValue (Lit v) _                = v

evalTerm :: Term v -> Env v -> Either (Output v) (Val v)
evalTerm (Embed v) env     = Right (evalValue v env)
evalTerm (Mu cmd) env      =
  case evalCommand cmd env of
    (0, val) -> Right val     -- slot 0 is the focus
    out      -> Left out      -- anything else escapes
evalTerm (ThenComatch cmd) env =
  let fwdA = case evalCommand cmd env of
               (1, v) -> v
               _      -> error "ThenComatch: expected slot 1 for fwd a"
      bwCont bwA =
        case evalCommand cmd (bwA : env) of
          (0, v) -> RVal 0 v
          out    -> uncurry RVal out
  in Right (VThen fwdA bwCont)

evalCoterm :: Coterm v -> Env v -> Val v -> Output v
evalCoterm (Covar i) _env val             = (i, val)
evalCoterm (Comu cmd) env val             = evalCommand cmd (val : env)
evalCoterm (TensorMatch cmd) env (VPair x y) = evalCommand cmd (x : y : env)
evalCoterm (TensorMatch _) _ v            = error $ "TensorMatch: not a pair: " <> show' v
evalCoterm (PlusMatch c1 _) env (VLeft x) = evalCommand c1 (x : env)
evalCoterm (PlusMatch _ c2) env (VRight y)= evalCommand c2 (y : env)
evalCoterm (PlusMatch _ _) _ v            = error $ "PlusMatch: not a sum: " <> show' v
evalCoterm (HomCointro t k) env f =
  case evalTerm t env of
    Left out  -> out
    Right arg -> case f of
      VFun g    -> let RVal _ v = g arg in evalCoterm k env v
      _         -> error "HomCointro: not a function"
evalCoterm (GradedHomCointro t coterms) env f =
  case evalTerm t env of
    Left out  -> out
    Right arg -> case f of
      VGradedFun g ->
        let RVal slot val = g arg
        in evalCoterm (coterms !! slot) env val
      _ -> error "GradedHomCointro: not a graded function"
evalCoterm (ThenCointro k1 k2) env val =
  case val of
    VThen fwdA cont ->
      let (_, residual) = evalCoterm k1 env fwdA
          RVal _ fwdB   = cont residual
      in evalCoterm k2 env fwdB
    _ -> error "ThenCointro: expected VThen"

-- | Helper for error messages without a Show constraint
show' :: Val v -> String
show' VUnit          = "VUnit"
show' (VPair _ _)    = "VPair"
show' (VLeft _)      = "VLeft"
show' (VRight _)     = "VRight"
show' (VFun _)       = "VFun"
show' (VGradedFun _) = "VGradedFun"
show' (VThen _ _)    = "VThen"
show' (VEmbed _)     = "VEmbed"

-- | Tests

-- identity via Hom: \x -> x applied to VUnit
-- HomComatch (Cut (Embed (Var 0)) (Covar 0))
testId :: Output ()
testId = evalCommand
  (Cut
    (Embed (HomComatch (Cut (Embed (Var 0)) (Covar 0))))
    (HomCointro (Embed (Var 0)) (Covar 0)))
  [VUnit]
-- expected: (0, VUnit)

-- Thread a Double through Then, identity on both sides
-- expected: (0, VEmbed 1.0)
testThen :: Output Double
testThen =
  let val = VThen (VEmbed 1.0) (\r -> RVal 0 r)
  in evalCommand
      (Cut
        (Embed (Lit val))
        (ThenCointro
          (Comu (Cut (Embed (Var 0)) (Covar 1)))  -- k1: fwdA -> slot 1 (residual)
          (Comu (Cut (Embed (Var 0)) (Covar 0))))) -- k2: fwdB -> slot 0 (focus)
      []

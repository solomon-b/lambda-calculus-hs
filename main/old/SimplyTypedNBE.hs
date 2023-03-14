{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StrictData #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Main where

--------------------------------------------------------------------------------

import Data.Functor (($>))

--------------------------------------------------------------------------------
-- Utils

data SnocList a
  = Snoc (SnocList a) a
  | Nil
  deriving (Show, Eq, Ord, Functor, Foldable)

nth :: SnocList a -> Int -> Maybe a
nth xs i
  | i < 0 = Nothing
  | otherwise =
      let go = \case
            (Nil, _) -> Nothing
            (Snoc _ x, 0) -> Just x
            (Snoc ys _, j) -> go (ys, j - 1)
       in go (xs, i)

--------------------------------------------------------------------------------
-- Terms

data Type = Type :-> Type | UnitT | BoolT
  deriving stock (Show, Eq, Ord)

newtype Env val
  = Env (SnocList val)
  deriving stock (Show, Eq, Ord, Functor)

initEnv :: Env val
initEnv = Env Nil

type Gamma = Env Type

initCtx :: Gamma
initCtx = initEnv

data Syntax
  = Var Ix
  | Abs Name Syntax
  | App Syntax Syntax
  | Unit
  | T
  | F
  | If Syntax Syntax Syntax
  | Anno Syntax Type
  deriving stock (Show, Eq, Ord)

data Value
  = VNeutral Type Neutral
  | VLam Name Closure
  | VTrue
  | VFalse
  | VUnit
  deriving stock (Show, Eq, Ord)

data Neutral = Neutral {head :: Head, spine :: SnocList Frame}
  deriving stock (Show, Eq, Ord)

newtype Head
  = VVar Lvl
  deriving (Show, Eq, Ord)

data Frame = VApp {ty :: Type, arg :: Value}
  deriving stock (Show, Eq, Ord)

pushFrame :: Neutral -> Frame -> Neutral
pushFrame Neutral {..} frame = Neutral {head = head, spine = Snoc spine frame}

data Closure = Closure {env :: Env Value, body :: Syntax}
  deriving stock (Show, Eq, Ord)

-- | Debruijn Indices
--
-- λ.λ.λ.2
-- ^-----^
newtype Ix
  = Ix Int
  deriving newtype (Show, Eq, Ord)

-- | Debruijn Levels
--
-- λ.λ.λ.0
-- ^-----^
newtype Lvl
  = Lvl Int
  deriving newtype (Show, Eq, Ord)

incLevel :: Lvl -> Lvl
incLevel (Lvl n) = Lvl (1 + n)

newtype Name
  = Name String
  deriving newtype (Show, Eq, Ord)

data Error
  = NotFound
  | TypeError String
  deriving (Show)

lookupVar :: Env val -> Ix -> Either Error val
lookupVar (Env env) (Ix i) = maybe (Left NotFound) Right $ env `nth` i

extend :: Env val -> val -> Env val
extend (Env env) val = Env (Snoc env val)

--------------------------------------------------------------------------------
-- Typechecking

synth :: Gamma -> Syntax -> Either Error Type
synth ctx = \case
  Var ix -> lookupVar ctx ix
  App t1 t2 ->
    synth ctx t1 >>= \case
      tyA :-> tyB -> do
        check ctx t2 tyA
        pure tyB
      ty -> Left (TypeError $ "Not a function type: " ++ show ty)
  T -> pure BoolT
  F -> pure BoolT
  Unit -> pure UnitT
  If t1 t2 t3 -> do
    check ctx t1 BoolT
    ty2 <- synth ctx t2
    ty3 <- synth ctx t3
    if ty2 == ty3
      then pure ty2
      else Left $ TypeError $ "Type mismatch: " <> show ty2 <> " /= " <> show ty3
  Anno t1 ty -> check ctx t1 ty $> ty
  _ -> Left $ TypeError "cannot synthesize type."

check :: Gamma -> Syntax -> Type -> Either Error ()
check ctx (Abs _bndr body) ty =
  case ty of
    tyA :-> tyB -> check (extend ctx tyA) body tyB
    ty' -> Left $ TypeError $ "Abs requires a function type, but got a: " <> show ty'
check ctx t1 ty = do
  ty' <- synth ctx t1
  if ty' == ty
    then pure ()
    else Left $ TypeError $ "Expected type " <> show ty <> " but got " <> show ty'

--------------------------------------------------------------------------------
-- Evaluation

eval :: Env Value -> Syntax -> Value
eval env = \case
  Var ix -> either (error "internal error") id $ lookupVar env ix
  Abs bndr body -> VLam bndr (Closure env body)
  App t1 t2 ->
    let fun = eval env t1
        arg = eval env t2
     in doApply fun arg
  T -> VTrue
  F -> VFalse
  Unit -> VUnit
  If t1 t2 t3 -> doIf (eval env t1) (eval env t2) (eval env t3)
  Anno t1 _ty -> eval env t1

doApply :: Value -> Value -> Value
doApply (VLam _ clo) arg =
  instantiateClosure clo arg
doApply (VNeutral (ty1 :-> ty2) neu) arg =
  VNeutral ty2 (pushFrame neu (VApp ty1 arg))
doApply _ _ = error "impossible case in doApply"

instantiateClosure :: Closure -> Value -> Value
instantiateClosure (Closure env body) v = eval (extend env v) body

doIf :: Value -> Value -> Value -> Value
doIf VTrue t2 _t3 = t2
doIf VFalse _t2 t3 = t3
doIf _ _ _ = error "impossible case in doIf"

quote :: Lvl -> Type -> Value -> Syntax
quote _ UnitT _ = Unit
quote _ BoolT VTrue = T
quote _ BoolT VFalse = F
quote l (tyA :-> tyB) (VLam bndr clo@(Closure _env _body)) =
  let body = bindVar tyA l $ \v l' ->
        quote l' tyB $ instantiateClosure clo v
   in Abs bndr body
quote l (tyA :-> tyB) f =
  let body = bindVar tyA l $ \v l' ->
        quote l' tyB (doApply f v)
   in Abs (Name "_") body
quote l ty1 (VNeutral ty2 neu) =
  if ty1 == ty2
    then quoteNeutral l neu
    else error "Internal error while quoting"
quote _ _ _ = error "impossible case in quote"

bindVar :: Type -> Lvl -> (Value -> Lvl -> a) -> a
bindVar ty lvl f =
  let v = VNeutral ty $ Neutral (VVar lvl) Nil
   in f v $ incLevel lvl

quoteLevel :: Lvl -> Lvl -> Ix
quoteLevel (Lvl l) (Lvl x) = Ix (l - (x + 1))

quoteNeutral :: Lvl -> Neutral -> Syntax
quoteNeutral l Neutral {..} = foldl (quoteFrame l) (quoteHead l head) spine

quoteHead :: Lvl -> Head -> Syntax
quoteHead l (VVar x) = Var (quoteLevel l x)

quoteFrame :: Lvl -> Syntax -> Frame -> Syntax
quoteFrame l t1 VApp {..} = App t1 (quote l ty arg)

normalize :: Syntax -> Syntax
normalize term =
  case synth initEnv term of
    Right ty ->
      let val = eval initEnv term
       in quote (Lvl 0) ty val
    Left err -> error $ show err

--------------------------------------------------------------------------------
-- main

-- λx. x
idenT :: Syntax
idenT = Anno (Abs (Name "x") (Var (Ix 0))) (UnitT :-> UnitT)

-- λf. f
identT' :: Syntax
identT' =
  Anno
    (Abs (Name "f") (Var (Ix 0)))
    ((BoolT :-> BoolT) :-> (BoolT :-> BoolT))

-- λx. λy. x
constT :: Syntax
constT = Anno (Abs (Name "x") (Abs (Name "_") (Var (Ix 1)))) (BoolT :-> (UnitT :-> BoolT))

-- λf. λx. f x
applyT :: Syntax
applyT =
  Anno
    (Abs (Name "f") (Abs (Name "x") (App (Var (Ix 1)) (Var (Ix 0)))))
    ((BoolT :-> BoolT) :-> (BoolT :-> BoolT))

notT :: Syntax
notT =
  Anno
    (Abs (Name "p") (If (Var (Ix 0)) T F))
    (BoolT :-> BoolT)

main :: IO ()
main = do
  let term = Anno (Abs (Name "f") (Var (Ix 0))) ((BoolT :-> BoolT) :-> (BoolT :-> BoolT))
  case synth initCtx term of
    Left err -> print err
    Right ty -> do
      print ty
      print (normalize term)

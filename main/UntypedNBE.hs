{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}

module Main where

--------------------------------------------------------------------------------

import Control.Monad.State
import Data.List ((\\))
import Data.Map (Map)
import qualified Data.Map.Strict as M

--------------------------------------------------------------------------------
-- Terms

data Term
  = Var Name
  | Abs Name Term
  | App Term Term
  deriving (Show)

data Value
  = VClosure (Env Value) Name Term
  | VNeutral Neutral
  deriving (Show)

data Neutral
  = NVar Name
  | NApp Neutral Value
  deriving (Show)

newtype Name = Name String
  deriving newtype (Show, Eq, Ord)

newtype Env val = Env [(Name, val)]
  deriving stock (Show, Functor)

initEnv :: Env val
initEnv = Env []

newtype Error = NotFound Name
  deriving (Show)

lookupVar :: Env val -> Name -> Either Error val
lookupVar (Env env) var = maybe (Left $ NotFound var) Right $ lookup var env

extend :: Env val -> Name -> val -> Env val
extend (Env env) var val = Env ((var, val) : env)

--------------------------------------------------------------------------------
-- Alpha Conversion

data Stream a = Stream a (Stream a)

data AlphaContext = AlphaContext {_names :: Stream Name, _register :: Map Name Name}

names :: [Name]
names = fmap Name $ (pure <$> ['a' .. 'z']) ++ (flip (:) <$> (show <$> [1 ..]) <*> ['a' .. 'z'])

stream :: [Name] -> Stream Name
stream (x : xs) = Stream x (stream xs)

alpha :: Term -> State AlphaContext Term
alpha = \case
  (Var x) -> do
    mx <- gets (M.lookup x . _register)
    case mx of
      Just x' -> pure $ Var x'
      Nothing -> error "Something impossible happened"
  (App t1 t2) -> do
    t1' <- alpha t1
    t2' <- alpha t2
    pure $ App t1' t2'
  t@(Abs bndr term) -> do
    (Stream fresh rest) <- gets _names
    registry <- gets _register
    put $ AlphaContext rest (M.insert bndr fresh registry)
    term' <- alpha term
    pure $ Abs fresh term'

emptyContext :: AlphaContext
emptyContext = AlphaContext (stream names) M.empty

alphaconvert :: Term -> Term
alphaconvert term = evalState (alpha term) emptyContext

--------------------------------------------------------------------------------
-- Evaluation

eval :: Env Value -> Term -> Either Error Value
eval env = \case
  Var x -> lookupVar env x
  Abs x body -> pure (VClosure env x body)
  App t1 t2 -> do
    fun <- eval env t1
    arg <- eval env t2
    doApply fun arg

doApply :: Value -> Value -> Either Error Value
doApply (VClosure env x body) arg =
  eval (extend env x arg) body
doApply (VNeutral neu) arg =
  Right (VNeutral (NApp neu arg))

quote :: [Name] -> Value -> Either Error Term
quote used = \case
  VNeutral (NVar x) -> pure (Var x)
  VNeutral (NApp fun arg) -> do
    t1 <- quote used (VNeutral fun)
    t2 <- quote used arg
    pure (App t1 t2)
  fun@(VClosure _ x _) -> do
    bodyVal <- doApply fun (VNeutral (NVar x))
    bodyTerm <- quote (x : used) bodyVal
    pure (Abs x bodyTerm)

normalize :: Term -> Either Error Term
normalize term = do
  val <- eval initEnv term
  quote [] val

--------------------------------------------------------------------------------
-- main

idenT :: Term
idenT = Abs (Name "x") (Var (Name "x"))

trueT :: Term
trueT = Abs (Name "p") (Abs (Name "a") (Var (Name "p")))

falseT :: Term
falseT = Abs (Name "p") (Abs (Name "q") (Var (Name "q")))

notT :: Term
notT = Abs (Name "p") (App (App (Var (Name "p")) falseT) trueT)

main :: IO ()
main = do
  let term = alphaconvert (App notT trueT)
  print (normalize term)

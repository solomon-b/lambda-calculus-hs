{-# LANGUAGE LambdaCase #-}
module Main where

import Data.Map (Map)
import qualified Data.Map.Strict as M
import Data.List ((\\))
import Control.Monad.State

-------------
--- Terms ---
-------------

data Term = Var String
          | Abs String Term
          | App Term Term
  deriving Show

------------------------
--- Alpha Conversion ---
------------------------

data Stream a = Stream a (Stream a)

data AlphaContext = AlphaContext { _names :: Stream String, _register :: Map String String }

names :: [String]
names = (pure <$> ['a'..'z']) ++ (flip (:) <$> (show <$> [1..]) <*> ['a' .. 'z'])

stream :: [String] -> Stream String
stream (x:xs) = Stream x (stream xs)

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
emptyContext = AlphaContext (stream names) (M.empty)

alphaconvert :: Term -> Term
alphaconvert term = evalState (alpha term) emptyContext

--------------------
--- Substitution ---
--------------------

subst :: String -> Term -> Term -> Term
subst x s = \case
  (Var x') | x == x' -> s
  (Var y) -> Var y
  (Abs y t1) | x /= y && y `notElem` freevars s -> Abs y (subst x s t1)
             | otherwise -> error "oops name collision"
  (App t1 t2) -> App (subst x s t1) (subst x s t2)

freevars :: Term -> [String]
freevars = \case
  (Var x) -> [x]
  (Abs x t) -> freevars t \\ [x]
  (App t1 t2) -> freevars t1 ++ freevars t2

------------------
--- Evaluation ---
------------------

isVal :: Term -> Bool
isVal = \case
  Abs{} -> True
  _     -> False

singleEval :: Term -> Maybe Term
singleEval = \case
  (App (Abs x t12) v2) | isVal v2 -> Just $ subst x v2 t12
  (App v1@Abs{} t2) -> App v1 <$> singleEval t2
  (App t1 t2) -> flip App t2 <$> singleEval t1
  _ -> Nothing

multiStepEval :: Term -> Term
multiStepEval t = maybe t multiStepEval (singleEval t)


------------
--- Main ---
------------

idenT :: Term
idenT = Abs "x" (Var "x")

trueT :: Term
trueT = Abs "p" (Abs "a" (Var "p"))

falseT :: Term
falseT = Abs "p" (Abs "q" (Var "q"))

notT :: Term
notT = Abs "p" (App (App (Var "p") falseT) trueT)

main :: IO ()
main = do
  let term = alphaconvert (App notT trueT)
  print (multiStepEval term)

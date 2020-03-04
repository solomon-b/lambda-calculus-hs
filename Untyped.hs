{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
module Main where

import Data.List ((\\))

-------------
--- Terms ---
-------------

data Term = Var String
          | Abs String Term
          | App Term Term
  deriving Show

------------------
--- Evaluation ---
------------------

isVal :: Term -> Bool
isVal Abs{} = True
isVal _ = False

subst :: String -> Term -> Term -> Term
subst x s (Var x') | x == x' = s
subst x s (Var y) = Var y
subst x s (Abs y t1) | x /= y && y `notElem` freevars s = Abs y (subst x s t1)
                     | otherwise = error "oops name collision"
subst x s (App t1 t2) = App (subst x s t1) (subst x s t2)

freevars :: Term -> [String]
freevars (Var x) = [x]
freevars (Abs x t) = freevars t \\ [x]
freevars (App t1 t2) = freevars t1 ++ freevars t2

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
trueT = Abs "p" (Abs "q" (Var "p"))

falseT :: Term
falseT = Abs "p "(Abs "q" (Var "q"))

notT :: Term
notT = Abs "p" (App (App (Var "p") falseT) trueT)

main :: IO ()
main =
  let term = (App notT trueT)
  in print (multiStepEval term)

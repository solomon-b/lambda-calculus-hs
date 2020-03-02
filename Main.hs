{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
module Main where

import Data.List
import Control.Monad.Reader
import Control.Monad.Except

data Term = Var String
          | Abs String Type Term
          | App Term Term
          | Z
          | S Term
          | Case Term String Term Term
  deriving (Show, Eq)

data Type = Type :-> Type | Nat
  deriving (Show, Eq)

type Context = [(String, Type)]

updateContext :: (String, Type) -> Context -> Context
updateContext = (:)

data TypeErr = TypeError deriving (Show, Eq)


--------------------
--- Typechecking ---
--------------------

newtype TypecheckM a =
  TypecheckM { unTypecheckT :: ExceptT TypeErr (Reader Context) a }
  deriving (Functor, Applicative, Monad, MonadReader Context, MonadError TypeErr)

typecheck :: Term -> TypecheckM Type
typecheck = \case
  Var x -> do
    ty <- lookup x <$> ask
    maybe (throwError TypeError) pure ty
  Abs _ ty1 trm -> do
    ty2 <- typecheck trm
    pure $ ty1 :-> ty2
  App t1 t2 -> do
    ty1 <- typecheck t1
    ty2 <- typecheck t2
    if ty1 == ty2 then pure ty1 else throwError TypeError
  Z -> pure Nat
  S n -> do
    ty <- typecheck n
    if ty == Nat then pure Nat else throwError TypeError
  Case t0 bndr t1 t2 -> do
    ty0 <- typecheck t0
    ty1 <- typecheck t1
    ty2 <- typecheck t2
    if ty0 == Nat && ty1 == ty2
      then pure ty1
      else throwError TypeError


------------------
--- Evaluation ---
------------------

isVal :: Term -> Bool
isVal Abs{} = True
isVal Z = True
isVal (S t) = isVal t
isVal _ = False

subst :: String -> Term -> Term -> Term
subst x v1 (Var y) | x == y = v1
subst x v1 (Var y) = Var y
subst x v1 (Abs y ty t1) | x == y = Abs y ty t1
                      | y `notElem` freevars v1 = Abs y ty (subst x v1 t1)
                      | otherwise = error "oops name collision"
subst x v1 (App t1 t2) = App (subst x v1 t1) (subst x v1 t2)

freevars :: Term -> [String]
freevars (Var x) = [x]
freevars (Abs x _ t) = freevars t \\ [x]
freevars (App t1 t2) = freevars t1 ++ freevars t2

singleEval :: Term -> Maybe Term
singleEval t =
  case t of
    (App (Abs x ty t12) v2) | isVal v2 -> Just $ subst x v2 t12
    (App v1@(Abs _ _ _) t2)           ->    App v1 <$> singleEval t2
    (App t1 t2)                     -> flip App t2 <$> singleEval t1
    _ -> Nothing

multiStepEval :: Term -> Term
multiStepEval t = maybe t multiStepEval (singleEval t)


caseExample :: Term
caseExample = undefined -- Abs "z" (App (App (Var "z") fls) tru)

main :: IO ()
main = print $ multiStepEval (App nt fls)

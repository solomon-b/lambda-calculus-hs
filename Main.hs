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
          | T
          | F
          | If Term Term Term
          | Rec Term Term
          | Case Term String Term Term
  deriving (Show, Eq)

data Type = Type :-> Type | Nat | Bool'
  deriving (Show, Eq)

type Context = [(String, Type)]
data TypeErr = TypeError deriving (Show, Eq)


--------------------
--- Typechecking ---
--------------------

newtype TypecheckM a =
  TypecheckM { unTypecheckM :: ExceptT TypeErr (Reader Context) a }
  deriving (Functor, Applicative, Monad, MonadReader Context, MonadError TypeErr)

runTypecheckM :: TypecheckM Type -> Either TypeErr Type
runTypecheckM = flip runReader [] . runExceptT . unTypecheckM

typecheck :: Term -> TypecheckM Type
typecheck = \case
  Var x -> do
    ty <- asks $ lookup x
    maybe (throwError TypeError) pure ty
  Abs bndr ty1 trm -> do
    ty2 <- local ((:) (bndr, ty1)) (typecheck trm)
    pure $ ty1 :-> ty2
  App t1 t2 -> do
    ty1 <- typecheck t1
    case ty1 of
      tyA :-> tyB -> do
        ty2 <- typecheck t2
        if tyA == ty2 then pure ty1 else throwError TypeError
      _ -> throwError TypeError
  Z -> pure Nat
  S n -> do
    ty <- typecheck n
    if ty == Nat then pure Nat else throwError TypeError
  Case t0 bndr t1 t2 -> do
    ty0 <- typecheck t0
    ty1 <- typecheck t1
    ty2 <- local ((:) (bndr, ty1)) (typecheck t2)
    if ty0 == Nat && ty1 == ty2
      then pure ty1
      else throwError TypeError
  T -> pure Bool'
  F -> pure Bool'
  If t0 t1 t2 -> do
    ty0 <- typecheck t0
    ty1 <- typecheck t1
    ty2 <- typecheck t2
    if ty0 == Bool' && ty1 == ty2
      then pure ty1
      else throwError TypeError
  Rec base step -> do
    ty0 <- typecheck base
    ty1 <- typecheck step
    case ty1 of
      Nat :-> (ty :-> ty') | ty == ty' -> pure (Nat :-> ty)
      ty -> throwError TypeError


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
subst x v1 (Case t0 bndr t1 t2) = Case (subst x v1 t0) bndr (subst x v1 t1) (subst x v1 t2)
subst x v1 Z = Z
subst x v1 (S t) = S (subst x v1 t)
subst x v1 T = T
subst x v1 F = F
subst x v1 (If t0 t1 t2) = If (subst x v1 t0) (subst x v1 t1) (subst x v1 t2)
subst x v1 (Rec base step) = Rec (subst x v1 base) (subst x v1 step)

freevars :: Term -> [String]
freevars (Var x) = [x]
freevars (Abs x _ t) = freevars t \\ [x]
freevars (App t1 t2) = freevars t1 ++ freevars t2
freevars (S t) = freevars t
freevars (Case t0 _ t1 t2) = freevars t0 ++ freevars t1 ++ freevars t2
freevars (If t0 t1 t2) = freevars t0 ++ freevars t1 ++ freevars t2
freevars (Rec t0 t1) = freevars t0 ++ freevars t1
freevars _ = []

singleEval :: Term -> Maybe Term
singleEval = \case
  (App (Abs x ty t12) v2) | isVal v2 -> Just $ subst x v2 t12
  (App v1@Abs{} t2) -> App v1 <$> singleEval t2
  (App (Rec base step) Z) -> pure base
  (App (Rec base step) (S n)) -> pure $ App (App step n) (App (Rec base step) n)
  (App t1 t2) -> flip App t2 <$> singleEval t1
  (S t) | not (isVal t) -> S <$> singleEval t
  (Case t0 bndr t1 t2) | not (isVal t0) -> singleEval t0 >>= \t0' -> pure $ Case t0' bndr t1 t2
  (Case v1 bndr t1 t2) | v1 == Z -> pure t1
  (Case (S v1) bndr t1 t2) -> Just $ subst bndr v1 t2
  (If T t2 t3) -> pure t2
  (If F t2 t3) -> pure t3
  _ -> Nothing

multiStepEval :: Term -> Term
multiStepEval t = maybe t multiStepEval (singleEval t)


--------------------
--- Sample Terms ---
--------------------

isZero :: Term
isZero = Abs "n" Nat (Case (Var "n") "m" Z (S Z))

iden :: Term
iden = Abs "n" Nat (Var "n")

add1 :: Term
add1 = Abs "step" Nat (Abs "n" Nat (S (Var "n")))

add :: Term
add = Abs "base" Nat (Rec (Var "base") add1)

main :: IO ()
main =
  let term = App (App add (S $ S Z)) (S $ S Z)
  in case runTypecheckM $ typecheck term of
    Left e -> print e
    Right ty -> print ty >> print (multiStepEval term)

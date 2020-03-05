{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
module Main where

import Data.Map (Map)
import qualified Data.Map.Strict as M
import Data.List ((\\))
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except

-------------
--- Terms ---
-------------

data Term = Var String
          | Abs String Type Term
          | App Term Term
          | Unit
          | T
          | F
          | If Term Term Term
  deriving Show

data Type = Type :-> Type | UnitT | BoolT
  deriving (Show, Eq)

type Gamma = [(String, Type)]

data TypeErr = TypeError deriving (Show, Eq)

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
  t@(Abs bndr ty term) -> do
    (Stream fresh rest) <- gets _names
    registry <- gets _register
    put $ AlphaContext rest (M.insert bndr fresh registry)
    term' <- alpha term
    pure $ Abs fresh ty term'
  (If t1 t2 t3) -> do
    t1' <- alpha t1
    t2' <- alpha t2
    t3' <- alpha t3
    pure (If t1' t2' t3')
  t -> pure t

emptyContext :: AlphaContext
emptyContext = AlphaContext (stream names) (M.empty)

alphaconvert :: Term -> Term
alphaconvert term = evalState (alpha term) emptyContext

--------------------
--- Typechecking ---
--------------------

newtype TypecheckM a =
  TypecheckM { unTypecheckM :: ExceptT TypeErr (Reader Gamma) a }
  deriving (Functor, Applicative, Monad, MonadReader Gamma, MonadError TypeErr)

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
  Unit -> pure UnitT
  T -> pure BoolT
  F -> pure BoolT
  If t0 t1 t2 -> do
    ty0 <- typecheck t0
    ty1 <- typecheck t1
    ty2 <- typecheck t2
    if ty0 == BoolT && ty1 == ty2
      then pure ty1
      else throwError TypeError

--------------------
--- Substitution ---
--------------------

subst :: String -> Term -> Term -> Term
subst x s = \case
  (Var x') | x == x' -> s
  (Var y) -> Var y
  (Abs y ty t1) | x /= y && y `notElem` freevars s -> Abs y ty (subst x s t1)
             | otherwise -> error "oops name collision"
  (App t1 t2) -> App (subst x s t1) (subst x s t2)
  (If t0 t1 t2) -> If (subst x s t0) (subst x s t1) (subst x s t2)
  T -> T
  F -> F
  Unit -> Unit

freevars :: Term -> [String]
freevars = \case
  (Var x)       -> [x]
  (Abs x ty t)  -> freevars t \\ [x]
  (App t1 t2)   -> freevars t1 ++ freevars t2
  (If t0 t1 t2) -> freevars t0 ++ freevars t1 ++ freevars t2

------------------
--- Evaluation ---
------------------

isVal :: Term -> Bool
isVal = \case
  Abs{} -> True
  T     -> True
  F     -> True
  Unit  -> True
  _     -> False

singleEval :: Term -> Maybe Term
singleEval = \case
  (App (Abs x ty t12) v2) | isVal v2 -> Just $ subst x v2 t12
  (App v1@Abs{} t2) -> App v1 <$> singleEval t2
  (App t1 t2) -> flip App t2 <$> singleEval t1
  (If T t2 t3) -> pure t2
  (If F t2 t3) -> pure t3
  _ -> Nothing

multiStepEval :: Term -> Term
multiStepEval t = maybe t multiStepEval (singleEval t)


------------
--- Main ---
------------

notT :: Term
notT = Abs "p" BoolT (If (Var "p") F T)

main :: IO ()
main =
  let term = alphaconvert (App notT T)
  in case runTypecheckM $ typecheck term of
    Left e -> print e
    Right _ -> print (multiStepEval term)

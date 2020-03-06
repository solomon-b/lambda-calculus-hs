{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
module Main where

import Data.Map (Map)
import qualified Data.Map.Strict as M
import Data.List ((\\))
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except

import Control.Lens

-------------
--- Terms ---
-------------

data Term = Var String
          | Abs String Type Term
          | App Term Term
          | TAbs String Term
          | TApp Term Type
          | Unit
          | T
          | F
          | If Term Term Term
  deriving Show

data Type = Type :-> Type | TVar String | Forall String Type | UnitT | BoolT
  deriving (Show, Eq)

data Gamma = Gamma { _context :: Map String Type, _contextT :: [String] }
makeLenses ''Gamma

data TypeErr = TypeError deriving (Show, Eq)

------------------------
--- Alpha Conversion ---
------------------------

data Stream a = Stream a (Stream a)

data AlphaContext = AlphaContext { _names :: Stream String, _register :: Map String String, _registerT :: Map String String}
makeLenses ''AlphaContext

namesStream :: [String]
namesStream = (pure <$> ['a'..'z']) ++ (flip (:) <$> (show <$> [1..]) <*> ['a' .. 'z'])

stream :: [String] -> Stream String
stream (x:xs) = Stream x (stream xs)

alphaT :: Type -> State AlphaContext Type
alphaT = \case
  TVar x -> do
    use (register . at x) >>= \case
      Just x' -> pure $ TVar x'
      Nothing -> error "Something impossible happened"
  Forall x ty -> do
    use (register . at x) >>= \case
      Just x' -> Forall x' <$> alphaT ty
      Nothing -> error "Something impossible happened"
  ty1 :-> ty2 -> do
    ty1' <- alphaT ty1
    ty2' <- alphaT ty2
    pure $ ty1' :-> ty2'
  t -> pure t

alpha :: Term -> State AlphaContext Term
alpha = \case
  Var x -> do
    use (register . at x) >>= \case
      Just x' -> pure $ Var x'
      Nothing -> error "Something impossible happened"
  App t1 t2 -> do
    t1' <- alpha t1
    t2' <- alpha t2
    pure $ App t1' t2'
  Abs bndr ty term -> do
    Stream fresh rest <- use names
    registry <- use register
    names .= rest
    register %= M.insert bndr fresh
    term' <- alpha term
    ty' <- alphaT ty
    pure $ Abs fresh ty' term'
  TApp t x -> do
    t' <- alpha t
    x' <- alphaT x
    pure $ TApp t' x'
  TAbs tyBndr term -> do
    Stream fresh rest <- use names
    names .= rest
    register %= M.insert tyBndr fresh
    term' <- alpha term
    pure $ TAbs fresh term'
  If t1 t2 t3 -> do
    t1' <- alpha t1
    t2' <- alpha t2
    t3' <- alpha t3
    pure (If t1' t2' t3')
  t -> pure t

emptyAlphaContext :: AlphaContext
emptyAlphaContext = AlphaContext (stream namesStream) M.empty M.empty

alphaconvert :: Term -> Term
alphaconvert term = evalState (alpha term) emptyAlphaContext

--------------------
--- Typechecking ---
--------------------

newtype TypecheckM a =
  TypecheckM { unTypecheckM :: ExceptT TypeErr (Reader Gamma) a }
  deriving (Functor, Applicative, Monad, MonadReader Gamma, MonadError TypeErr)

emptyGamma :: Gamma
emptyGamma = Gamma mempty mempty

runTypecheckM :: TypecheckM Type -> Either TypeErr Type
runTypecheckM = flip runReader emptyGamma . runExceptT . unTypecheckM

typecheck :: Term -> TypecheckM Type
typecheck = \case
  Var x -> do
    ty <- view (context . at x)
    maybe (throwError TypeError) pure ty
  Abs bndr ty1 trm -> do
    ty2 <- local (context %~ M.insert bndr ty1) (typecheck trm)
    pure $ ty1 :-> ty2
  App t1 t2 ->
    typecheck t1 >>= \case
      tyA :-> tyB -> do
        ty2 <- typecheck t2
        if tyA == ty2 then pure tyB else throwError TypeError
      _ -> throwError TypeError
  TAbs x t2 -> Forall x <$> typecheck t2
  TApp t1 ty2 ->
    typecheck t1 >>= \case
      Forall x ty12 -> pure $ substT x ty2 ty12 -- [x -> ty2]ty12
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

substTyTm :: String -> Type -> Term -> Term
substTyTm x s = \case
  Abs y ty t1 -> Abs y (substT x s ty) t1
  App t1 t2 -> App (substTyTm x s t1) (substTyTm x s t2)
  If t0 t1 t2 -> If (substTyTm x s t0) (substTyTm x s t1) (substTyTm x s t2)
  t -> t

substT :: String -> Type -> Type -> Type
substT x s = \case
  TVar x' | x == x' -> s
  TVar y ->  TVar y
  Forall y ty | x /= y -> Forall y (substT x s ty)
  ty1 :-> ty2 -> substT x s ty1 :-> substT x s ty2
  ty -> ty

subst :: String -> Term -> Term -> Term
subst x s = \case
  Var x' | x == x' -> s
  Var y -> Var y
  Abs y ty t1 | x /= y && y `notElem` freevars s -> Abs y ty (subst x s t1)
            | otherwise -> error "oops name collision"
  App t1 t2 -> App (subst x s t1) (subst x s t2)
  If t0 t1 t2 -> If (subst x s t0) (subst x s t1) (subst x s t2)
  T -> T
  F -> F
  Unit -> Unit

freevars :: Term -> [String]
freevars = \case
  Var x       -> [x]
  Abs x ty t  -> freevars t \\ [x]
  App t1 t2   -> freevars t1 ++ freevars t2
  If t0 t1 t2 -> freevars t0 ++ freevars t1 ++ freevars t2

------------------
--- Evaluation ---
------------------

isVal :: Term -> Bool
isVal = \case
  Abs{}  -> True
  TAbs{} -> True
  T      -> True
  F      -> True
  Unit   -> True
  _      -> False

singleEval :: Term -> Maybe Term
singleEval = \case
  App (Abs x ty t12) v2 | isVal v2 -> Just $ subst x v2 t12
  App v1@Abs{} t2 -> App v1 <$> singleEval t2
  App t1 t2 -> flip App t2 <$> singleEval t1
  TApp (TAbs x t12) ty2 -> Just (substTyTm x ty2 t12)
  TApp t1 ty2 -> flip TApp ty2 <$> singleEval t1
  If T t2 t3 -> pure t2
  If F t2 t3 -> pure t3
  _ -> Nothing

multiStepEval :: Term -> Term
multiStepEval t = maybe t multiStepEval (singleEval t)

------------
--- Main ---
------------

idenT :: Term
idenT = TAbs "X" (Abs "t" (TVar "X") (Var "t"))

notT :: Term
notT = Abs "p" BoolT (If (Var "p") F T)

main :: IO ()
main =
  let term = alphaconvert (App (TApp idenT BoolT) T)
  in case runTypecheckM $ typecheck term of
    Left e -> print e
    Right ty -> do
      print term
      putStrLn $ show (multiStepEval term) ++ " : " ++ show ty

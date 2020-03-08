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
          | Unit
          | T
          | F
          | If Term Term Term
  deriving Show

infixr 0 :->
data Type = Type :-> Type
          | TVar String
          | TyAbs String Kind Type
          | TyApp Type Type
          | UnitT
          | BoolT
  deriving (Show, Eq)

infixr 0 :=>
data Kind = Star | Kind :=> Kind
  deriving (Show, Eq)

data Gamma =
  Gamma { _context :: Map String Type
        , _contextT :: Map String Kind
        }
makeLenses ''Gamma

data TypeErr = TypeError | KindError deriving (Show, Eq)

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
--- Kindchecking ---
--------------------

kindcheck :: Type -> TypecheckM Kind
kindcheck (TVar bndr) = do --M.lookup bndr gamma
    k1 <- view (contextT . at bndr)
    maybe (throwError KindError) pure k1
kindcheck (TyAbs bndr k1 ty) = do
  k2 <- local (contextT %~ M.insert bndr k1) (kindcheck ty)
  pure $ k1 :=> k2
kindcheck (TyApp ty1 ty2) =
  kindcheck ty1 >>= \case
    k11 :=> k12 ->
      kindcheck ty2 >>= \k2 ->
        if k2 == k11 then pure k12 else throwError KindError
    _ -> throwError KindError
kindcheck (ty1 :-> ty2) = do
  k1 <- kindcheck ty1
  k2 <- kindcheck ty2
  if (k1, k2) == (Star, Star) then pure Star else throwError KindError

------------------------
--- Type Equivalence ---
------------------------

-- NOTE: This comes into play in the T-Eq typing rule
-- NOTE: I think I need a unification function similar to SystemF for TVars
tyeq :: Type -> Type -> Bool
tyeq (s1 :-> s2) (t1 :-> t2) = tyeq s1 t1 && tyeq s2 t2
tyeq (TyAbs b1 k1 s2) (TyAbs b2 k2 t2) = k1 == k2 && s2 == t2
tyeq (TyApp (TyAbs b1 k11 s12) s2) t1 =
  tyeq (substT b1 t1 s12) t1
tyeq s1 (TyApp (TyAbs b2 k11 t12) s2) =
  tyeq s1 (substT b2 s1 t12)
tyeq (TyApp s1 s2) (TyApp t1 t2) = s1 == t1 && s2 == t2
tyeq s1 t1 = s1 == t1

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

-- NOTE: Where does the T-Eq Typing rule come into play?
-- Gamma |- t : S   S === T   Gamma |- T : *
-- ----------------------------------------- T-Eq
--               Gamma |- t : T
typecheck :: Term -> TypecheckM Type
typecheck = \case
  Var x -> do
    ty <- view (context . at x)
    maybe (throwError TypeError) pure ty
  Abs bndr ty1 trm ->
    kindcheck ty1 >>= \case
      Star -> do
        ty2 <- local (context %~ M.insert bndr ty1) (typecheck trm)
        pure $ ty1 :-> ty2
      _ -> throwError KindError
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

substT :: String -> Type -> Type -> Type
substT x s = \case
  TVar x' | x == x' -> s
  TVar y ->  TVar y
  TyAbs y k ty | x /= y -> TyAbs y k (substT x s ty)
  TyAbs y k ty -> error "substT: oops name collision"
  TyApp ty1 ty2 -> TyApp (substT x s ty1) (substT x s ty2)
  ty1 :-> ty2 -> substT x s ty1 :-> substT x s ty2
  ty -> ty

subst :: String -> Term -> Term -> Term
subst x s = \case
  (Var x') | x == x' -> s
  (Var y) -> Var y
  (Abs y ty t1) | x /= y && y `notElem` freevars s -> Abs y ty (subst x s t1)
             | otherwise -> error "subst: oops name collision"
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

{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Main where

--------------------------------------------------------------------------------

import Data.Foldable (sequenceA_)
import Data.Maybe (fromMaybe)
import Data.String

--------------------------------------------------------------------------------
-- Utils

data SnocList a
  = Snoc (SnocList a) a
  | Nil
  deriving (Show, Eq, Ord, Functor, Foldable)

zipSnocWith :: (a -> b -> c) -> SnocList a -> SnocList b -> SnocList c
zipSnocWith f = go
  where
    go Nil _ = Nil
    go _ Nil = Nil
    go (Snoc as a) (Snoc bs b) = Snoc (go as bs) (f a b)

zipSnocWithM_ :: (Applicative m) => (a -> b -> m c) -> SnocList a -> SnocList b -> m ()
zipSnocWithM_ f xs ys = sequenceA_ (zipSnocWith f xs ys)

nth :: SnocList a -> Int -> Maybe a
nth xs i
  | i < 0 = Nothing
  | otherwise =
      let go = \case
            (Nil, _) -> Nothing
            (Snoc _ x, 0) -> Just x
            (Snoc xs' _, i') -> go (xs', i' - 1)
       in go (xs, i)

--------------------------------------------------------------------------------
-- Types

data Term
  = Var Ix
  | Lam Name Term
  | Ap Term Term
  | Pair Term Term
  | Fst Term
  | Snd Term
  | Unit
  | Anno Type Term
  deriving stock (Show, Eq, Ord)

data Type = FuncTy Type Type | PairTy Type Type | UnitTy
  deriving stock (Show, Eq, Ord)

data Value
  = VLam Name Closure
  | VPair Value Value
  | VUnit
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

newtype Name = Name {getName :: String}
  deriving newtype (Show, Eq, Ord, IsString)

data Closure = Closure {env :: SnocList Value, body :: Term}
  deriving stock (Show, Eq, Ord)

--------------------------------------------------------------------------------
-- Environment

newtype Env = Env { getEnv :: SnocList Type }
  deriving stock (Show, Eq, Ord)

initEnv :: Env
initEnv = Env Nil

extendEnv :: Env -> Type -> Env
extendEnv (Env env) ty = Env (Snoc env ty)

resolveVar :: Env -> Ix -> Maybe Type
resolveVar ctx (Ix ix) = nth (getEnv ctx) ix

--------------------------------------------------------------------------------
-- Typechecker

data Error
  = TypeError String
  | OutOfScopeError Ix
  deriving (Show)

synth :: Env -> Term -> Either Error Type
synth ctx = \case
  Var ix -> varTactic ctx ix
  Ap tm1 tm2 -> apTactic ctx tm1 tm2
  Anno ty tm -> check ctx ty tm
  Unit -> pure UnitTy
  tm -> Left $ TypeError $ "Cannot synthesize type for " <> show tm

check :: Env -> Type -> Term -> Either Error Type
check ctx (FuncTy ty1 ty2) (Lam _bndr tm) = lamTactic ctx ty1 ty2 tm
check ctx ty tm =
  case synth ctx tm of
    Right ty2 | ty == ty2 -> pure ty
    Right ty2 -> Left $ TypeError $ "Expected: " <> show ty <> ", but got: " <> show ty2
    Left err -> Left err

varTactic :: Env -> Ix -> Either Error Type
varTactic ctx ix =
  maybe (Left $ OutOfScopeError ix) Right $ resolveVar ctx ix

lamTactic :: Env -> Type -> Type -> Term -> Either Error Type
lamTactic ctx ty1 ty2 body = do
  _ <- check (extendEnv ctx ty1) ty2 body
  pure $ FuncTy ty1 ty2

apTactic :: Env -> Term -> Term -> Either Error Type
apTactic ctx tm1 tm2 =
  synth ctx tm1 >>= \case
    FuncTy ty1 ty2 -> do
      _ <- check ctx ty1 tm2
      pure ty2
    ty -> Left $ TypeError $ "Expected a function type but got " <> show ty

--------------------------------------------------------------------------------
-- Evaluator

eval :: SnocList Value -> Term -> Value
eval env = \case
  Var (Ix ix) -> fromMaybe (error "internal error") $ nth env ix
  Lam bndr body -> VLam bndr (Closure env body)
  Ap tm1 tm2 ->
    let fun = eval env tm1
        arg = eval env tm2
     in doApply fun arg
  Pair tm1 tm2 ->
    let tm1' = eval env tm1
        tm2' = eval env tm2
     in VPair tm1' tm2'
  Fst tm -> doFst $ eval env tm
  Snd tm -> doSnd $ eval env tm
  Anno _ty tm -> eval env tm
  Unit -> VUnit

doApply :: Value -> Value -> Value
doApply (VLam _ clo) arg =
  instantiateClosure clo arg
doApply _ _ = error "impossible case in doApply"

doFst :: Value -> Value
doFst (VPair a _b) = a
doFst _ = error "impossible case in doFst"

doSnd :: Value -> Value
doSnd (VPair _a b) = b
doSnd _ = error "impossible case in doSnd"

instantiateClosure :: Closure -> Value -> Value
instantiateClosure (Closure env body) v = eval (Snoc env v) body

--------------------------------------------------------------------------------
-- Main

main :: IO ()
main =
  let term' = idenT
   in case synth initEnv term' of
        Left err -> print err
        Right _ ->
          print $ eval Nil idenT'

-- λx. x
idenT :: Term
idenT =
  Anno
    (UnitTy `FuncTy` UnitTy)
    (Lam (Name "x") (Var (Ix 0)))

-- λf. f
idenT' :: Term
idenT' =
  Anno
    ((UnitTy `FuncTy` UnitTy) `FuncTy` (UnitTy `FuncTy` UnitTy))
    (Lam (Name "f") (Var (Ix 0)))

-- λx. λy. x
constT :: Term
constT =
  Anno
    (UnitTy `FuncTy` (UnitTy `FuncTy` UnitTy))
    (Lam (Name "x") (Lam (Name "_") (Var (Ix 1))))

-- λf. λx. f x
applyT :: Term
applyT =
  Anno
    ((UnitTy `FuncTy` UnitTy) `FuncTy` (UnitTy `FuncTy` UnitTy))
    (Lam (Name "f") (Lam (Name "x") (Ap (Var (Ix 1)) (Var (Ix 0)))))

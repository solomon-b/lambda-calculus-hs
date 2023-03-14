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
doApply (VLam _ clo) arg = instantiateClosure clo arg
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

run :: Term -> Value
run = eval Nil

main :: IO ()
main = print $ run (Ap idenT' Unit)

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
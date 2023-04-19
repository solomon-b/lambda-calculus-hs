{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Main where

--------------------------------------------------------------------------------

import Data.Maybe (fromMaybe)
import Data.String

--------------------------------------------------------------------------------
-- Utils

data SnocList a
  = Snoc (SnocList a) a
  | Nil
  deriving (Show, Eq, Ord, Functor, Foldable)

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

-- | 'Term' represents the concrete syntax of our langage generated
-- from text by a parser.
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

data Type
  = FuncTy Type Type
  | PairTy Type Type
  | UnitTy
  deriving stock (Show, Eq, Ord)

-- | 'Value' is the evaluated form of expressions in our language.
data Value
  = VLam Name Closure
  | VPair Value Value
  | VUnit
  deriving stock (Show, Eq, Ord)

-- | Debruijn Indices
--
-- 'Ix' is used to reference lambda bound terms with respect to
-- α-conversion. The index 'n' represents the value bound by the 'n'
-- lambda counting outward from the site of the index.
--
-- λ.λ.λ.2
-- ^-----^
newtype Ix
  = Ix Int
  deriving newtype (Show, Eq, Ord)

-- | Debruijn Levels
--
-- Similar to Debruijn Indices but counting inward from the outermost
-- lambda.
--
-- λ.λ.λ.0
-- ^-----^
--
-- Levels eliminate the need to reindex free variables when weakening
-- the context. This is useful in our 'Value' representation of
-- lambdas where we have a 'Closure' holding a stack of free variables.
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

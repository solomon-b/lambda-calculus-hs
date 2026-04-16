{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -ddump-simpl -dsuppress-all -dno-suppress-type-signatures -ddump-to-file -dno-typeable-binds #-}

{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE BangPatterns #-}
{- HLINT ignore "Avoid lambda" -}
{- HLINT ignore "Use id" -}
-- | The Krivine Abstract Machine.
module Main where

import Prelude hiding (succ)

import Control.Exception (evaluate)

import Data.Monoid
import Data.Semigroup

-- * Syntax

-- | The abstract syntax tree of our language.
data Term
  = Var Idx
  | Lam Term
  | App Term Term
  | Pair Term Term
  | Fst Term
  | Snd Term
  | Zero
  | Succ Term
  | Crash
  -- ^ Bottom value; crash.
  deriving stock (Show, Eq, Ord)

-- | De Bruijn Indices.
newtype Idx = Idx Int
  deriving stock (Show, Eq, Ord)

-- * Values

-- | A weak-head normal form term.
data Whnf
  = WLam Term
  -- ^ A lambda is in weak-head normal form.
  | WPair Term Term
  -- ^ A pair is in weak-head normal form.
  | WNat Word
  -- ^ We treat numbers as strict, so weak-head normal forms
  -- will be literals.
  | WCrash
  -- ^ A term that encountered a bottom is in WHNF.
  deriving stock (Show, Eq, Ord)

-- | A closure.
data Clo a = Clo Env a
  deriving stock (Show, Eq, Ord)

-- | Values are closures around weak-head normal form terms.
type Val = Clo Whnf

-- | An environment consists of a list of term closures.
data Env
  = ENil
  | ESnoc Env (Clo Term)
  deriving stock (Show, Eq, Ord)

-- | Lookup a de Bruijn index in an environment.
lookupEnv :: Idx -> Env -> Maybe (Clo Term)
lookupEnv (Idx n) e = loop n e
  where
    loop :: Int -> Env -> Maybe (Clo Term)
    loop _ ENil = Nothing
    loop 0 (ESnoc _ clo) = Just clo
    loop n (ESnoc e _) = loop (n - 1) e

-- * The Abstract Machine
--
-- An interpreter would evaluate our language by walking the syntax
-- tree, and building a value "on the way back up". This requires
-- us to make a bunch of recursive calls to our evaluator that
-- are not tail-calls. This can be rather inefficient[^1], as it
-- can lead to us allocating huge numbers of stack frames.
-- Moreover, a tree-walking interpreter is something that is difficult
-- to turn into a compiler for similar reasons: it's just not a very
-- machine-friendly algorithm.
--
-- To fix this, we can use an *abstract machine* to evaluate our code.
-- Abstract machines are essentially defunctionalizations of
-- tree-walking interpreters: any time we see something that could
-- be machine-unfriendly (stack usage, substitution, etc.) we will
-- reify it into an actual datastructure. The abstract machine will
-- then interpret expressions as if they were instructions, and use
-- them to update the various datastructures. When done correctly,
-- this lets us only ever perform tail-calls.
--
-- The particular abstract machine this file implements is the
-- *Krivine abstract machine*, which simulates call-by-name reduction
-- to weak-head normal form.
--
-- [^1]: This is a bit of a subtle point in Haskell, but the
-- subtleties are not relevant to the code we are writing!

-- | The stack, reified as a data structure.
data Stack
  = SNil
  -- ^ An empty stack.
  | SApp (Clo Term) Stack
  -- ^ Apply a term that we haven't evaluated yet.
  | SFst Stack
  -- ^ Apply a first projection.
  | SSnd Stack
  -- ^ Apply a second projection.
  | SSucc Stack
  -- ^ Take a successor.

-- | The Krivine abstract machine.
krivine :: Term -> Env -> Stack -> Val
krivine (Var i) e k =
  case lookupEnv i e of
    Just (Clo e' t) -> krivine t e' k
    Nothing -> error "krivine: ill-scoped environment for Var"
krivine (Lam t) e k =
  case k of
    SNil -> Clo e (WLam t)
    SApp v k -> krivine t (ESnoc e v) k
    _ -> error "krivine: ill-typed frame for Lam"
krivine (App t1 t2) e k = krivine t1 e (SApp (Clo e t2) k)
krivine (Pair t1 t2) e k =
  case k of
    SNil -> Clo e (WPair t1 t2)
    SFst k -> krivine t1 e k
    SSnd k -> krivine t2 e k
    _ -> error "krivine: ill-typed frame for Pair"
krivine (Fst t) e k = krivine t e (SFst k)
krivine (Snd t) e k = krivine t e (SSnd k)
krivine Zero e k = unwindSuccs 0 e k
krivine (Succ t) e k = krivine t e (SSucc k)
krivine Crash e _ = Clo e WCrash

-- | Unwind a stack of successors.
unwindSuccs :: Word -> Env -> Stack -> Val
unwindSuccs n e SNil = Clo e (WNat n)
unwindSuccs !n e (SSucc k) = unwindSuccs (1 + n) e k
unwindSuccs _ _ _ = error "unwindSuccs: ill-typed frame for Nat"

-- * HOAS Kit

newtype TermBuilder a = TermBuilder { runTermBuilder :: Int -> a }
  deriving (Functor, Applicative, Monad)

closed :: TermBuilder Term -> Term
closed t = runTermBuilder t 0

scope :: (TermBuilder Term -> TermBuilder r) -> TermBuilder r
scope k = TermBuilder \n ->
  let t = TermBuilder \n' -> Var (Idx (n' - n - 1))
  in runTermBuilder (k t) (n + 1)

lam :: (TermBuilder Term -> TermBuilder Term) -> TermBuilder Term
lam k = Lam <$> scope k

app :: TermBuilder Term -> TermBuilder Term -> TermBuilder Term
app = liftA2 App

appN :: TermBuilder Term -> [TermBuilder Term] -> TermBuilder Term
appN = foldl app

pair :: TermBuilder Term -> TermBuilder Term -> TermBuilder Term
pair = liftA2 Pair

fst_ :: TermBuilder Term -> TermBuilder Term
fst_ = fmap Fst

snd_ :: TermBuilder Term -> TermBuilder Term
snd_ = fmap Snd

zero :: TermBuilder Term
zero = pure Zero

succ :: TermBuilder Term -> TermBuilder Term
succ = fmap Succ

crash :: TermBuilder Term
crash = pure Crash

-- * Examples

-- | constant functions.
constT :: Term
constT = closed $ lam \x -> lam \_ -> x

-- | Create a church numeral.
churchT :: Word -> Term
churchT n = closed $ lam \s -> lam \z -> appEndo (stimes n (Endo (app s))) z

-- | Read back a church numeral to a number.
unChurchT :: Term
unChurchT = closed $ lam \x -> x `app` lam succ `app` zero

-- | Addition of church numerals.
addT :: Term
addT = closed $ lam \x -> lam \y -> lam \s -> lam \z -> x `app` s `app` (y `app` s `app` z)

main :: IO ()
main = do
  Clo _ (WNat n) <- evaluate (krivine (addT `App` churchT 1000 `App` churchT 1000) ENil SNil)
  print n

{- HLINT ignore "Redundant lambda" -}
{- HLINT ignore "Avoid lambda" -}
{- HLINT ignore "Use fmap" -}

{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE MagicHash #-}

-- | A variant of the spineless tagless G-machine.
module Main where

import Prelude hiding (succ)

import Control.Monad.ST
import Control.Exception (evaluate)

import Data.STRef

import Debug.Trace

import GHC.Exts (Word(..), Word#, plusWord#)
import GHC.Profiling.Eras

import Utils (SnocList(..), nth, iter)

-- * Syntax

-- | The abstract syntax tree of our language.
data Term
  = Var Idx
  | Lam Term
  | App Term Term
  | Pair Term Term
  | Fst Term
  | Snd Term
  | Word Word
  | Inc Word Term
  | Seq Term Term
  deriving stock (Show, Eq, Ord)

-- | De Bruijn Indices.
newtype Idx = Idx { unIdx :: Int }
  deriving stock (Show, Eq, Ord)

newtype Lvl = Lvl Int
  deriving stock (Show, Eq, Ord)

-- * The Heap

-- | An environment is just a list of pointers into the heap.
type Env s = SnocList (StgPtr s)

-- | A heap cell consists of either a thunk.
data HeapCell s
  = HThunk (Env s) Term
  | HClosure (Env s) Term
  | HTuple (Env s) Term Term
  | HWord Word#
  | HIndirect (StgPtr s)
  | HNeu (Neu s)

newtype StgPtr s = StgPtr { unStgPtr :: STRef s (HeapCell s) }

{-# INLINE newStgPtr #-}
newStgPtr :: HeapCell s -> ST s (StgPtr s)
newStgPtr = \c -> StgPtr <$> (newSTRef $! c)

{-# INLINE readStgPtr #-}
readStgPtr :: StgPtr s -> ST s (HeapCell s)
readStgPtr = readSTRef . unStgPtr

{-# INLINE writeStgPtr #-}
writeStgPtr :: StgPtr s -> HeapCell s -> ST s ()
writeStgPtr = \p c -> writeSTRef (unStgPtr p) $! c

data Neu s
  = NVar Lvl
  | NApp (StgPtr s) (StgPtr s)
  | NFst (StgPtr s)
  | NSnd (StgPtr s)
  | NInc Word# (StgPtr s)
  | NSeq (StgPtr s) (StgPtr s)

-- * The stack

data Stack s
  = SNil
  -- ^ Empty stack
  | SApp (StgPtr s) (Stack s)
  -- ^ Function arguments.
  | SUpdate (StgPtr s) (Stack s)
  -- ^ Update a thunk.
  --
  -- We push @SUpdate p@ frames when we begin
  -- evaluating a thunk.
  | SFst (Stack s)
  | SSnd (Stack s)
  | SInc Word# (Stack s)
  | SSeq (StgPtr s) (Stack s)

stg :: Term -> Env s -> Stack s -> ST s (StgPtr s)
stg (Var i) e k = do
  case nth e (unIdx i) of
    Just p -> do
      chaseVar p e k
    Nothing ->
      error "stg: out of bounds variable"
stg (Lam t) e k = do
  case k of
    SApp p k -> do
      stg t (Snoc e p) k
    _ -> do
      p <- newStgPtr (HClosure e t)
      unwindLam e t p k
stg (App t1 t2) e k = do
  p <- newStgPtr (HThunk e t2)
  stg t1 e (SApp p k)
stg (Pair t1 t2) e k =
  case k of
    SFst k ->
      stg t1 e k
    SSnd k ->
      stg t2 e k
    _ -> do
      p <- newStgPtr (HTuple e t1 t2)
      unwindTuple e t1 t2 p k
stg (Fst t) e k = do
  stg t e (SFst k)
stg (Snd t) e k = do
  stg t e (SSnd k)
stg (Word (W# n)) _e k = do
  unwindWord n k
stg (Inc (W# i) t) e k = do
  case k of
    SInc n k -> stg t e (SInc (i `plusWord#` n) k)
    _ -> stg t e (SInc 1## k)
stg (Seq t1 t2) e k = do
  p <- newStgPtr (HThunk e t2)
  stg t1 e (SSeq p k)

forceThunk :: StgPtr s -> Stack s -> ST s (StgPtr s)
forceThunk p k =
  readStgPtr p >>= \case
    HThunk e t -> stg t e k
    _ -> error "forceThunk: tried to force a pointer that did not point to a thunk."

-- | Chase a pointer.
chaseVar :: StgPtr s -> Env s -> Stack s -> ST s (StgPtr s)
chaseVar p e k =
  readStgPtr p >>= \case
    HThunk e' t -> do
      -- Start forcing the thunk.
      stg t e' (SUpdate p k)
    HClosure e' t ->
      unwindLam e' t p k
    HIndirect q ->
      -- Chase indirection pointers until we hit something useful.
      chaseVar q e k
    HTuple e t1 t2 ->
      -- If we hit a tuple, we want to unwind the stack to find
      -- a frame that's trying to project.
      unwindTuple e t1 t2 p k
    HWord n ->
      -- We don't pass in @p@ here, as we won't be writing indirections.
      unwindWord n k
    HNeu _ ->
      unwindNeu p k

unwindLam :: Env s -> Term -> StgPtr s -> Stack s -> ST s (StgPtr s)
unwindLam e t _p (SApp q k) = do
  stg t (Snoc e q) k
unwindLam e t p (SUpdate q k) = do
  writeStgPtr q (HIndirect p)
  unwindLam e t p k
unwindLam _e _t _p (SSeq q k) = do
  forceThunk q k
unwindLam _e _t p SNil = do
  pure p
unwindLam _e _t _p _k =
  error "unwindLam: ill-typed frame for a lambda"

unwindTuple :: Env s -> Term -> Term -> StgPtr s -> Stack s -> ST s (StgPtr s)
unwindTuple e t1 _t2 _p (SFst k) =
  stg t1 e k
unwindTuple e _t1 t2 _p (SSnd k) =
  stg t2 e k
unwindTuple e t1 t2 p (SUpdate q k) = do
  writeStgPtr q (HIndirect p)
  unwindTuple e t1 t2 p k
unwindTuple _e _t1 _t2 _p (SSeq q k) = do
  forceThunk q k
unwindTuple _e _t1 _t2 p SNil =
  pure p
unwindTuple _e _t1 _t2 _p _k =
  error "unwindTuple: ill-typed frame for a typle"

unwindWord :: Word# -> Stack s -> ST s (StgPtr s)
unwindWord !n (SInc i k) = do
  unwindWord (n `plusWord#` i) k
unwindWord n (SUpdate p k) = do
  -- Unlike the other unwinding functions, we do not introduce indirections.
  -- This is because there is no point trying to share the result of a
  -- strict 'Word' computation, as the size of an 'Indirect' cell is the same
  -- as the size of a 'Word'!
  writeStgPtr p (HWord n)
  unwindWord n k
unwindWord _n (SSeq p k) = do
  forceThunk p k
unwindWord n SNil = do
  newStgPtr (HWord n)
unwindWord _n _k =
  error "unwindWord: ill-typed frame for a nat"

unwindNeu :: StgPtr s -> Stack s -> ST s (StgPtr s)
unwindNeu p (SUpdate q k) = do
  writeStgPtr q (HIndirect p)
  unwindNeu p k
unwindNeu p (SSeq q k) = do
  r <- newStgPtr (HNeu (NSeq p q))
  unwindNeu r k
unwindNeu p (SApp q k) = do
  r <- newStgPtr (HNeu (NApp p q))
  unwindNeu r k
unwindNeu p (SFst k) = do
  q <- newStgPtr (HNeu (NFst p))
  unwindNeu q k
unwindNeu p (SSnd k) = do
  q <- newStgPtr (HNeu (NSnd p))
  unwindNeu q k
unwindNeu p (SInc n k) = do
  q <- newStgPtr (HNeu (NInc n p))
  unwindNeu q k
unwindNeu p SNil =
  pure p

-- * Readback

readback :: StgPtr s -> Word -> ST s Term
readback p !size =
  readStgPtr p >>= \case
    HThunk e t -> do
      q <- stg t e (SUpdate p SNil)
      readback  q size
    HClosure e t -> do
      q <- newStgPtr (HNeu (NVar (Lvl (length e))))
      r <- stg t (Snoc e q) SNil
      readback r (size + 1)
    HTuple e t1 t2 -> do
      q1 <- stg t1 e SNil
      q2 <- stg t2 e SNil
      Pair <$> readback q1 size <*> readback q2 size
    HWord w -> pure $ Word (W# w)
    HIndirect q ->
      readback q size
    HNeu n ->
      readbackNeu n size

readbackNeu :: Neu s -> Word -> ST s Term
readbackNeu (NVar (Lvl lvl)) size = pure $ Var (Idx (fromIntegral size - lvl - 1))
readbackNeu (NApp p q) size = App <$> readback p size <*> readback q size
readbackNeu (NFst p) size = Fst <$> readback p size
readbackNeu (NSnd p) size = Snd <$> readback p size
readbackNeu (NInc w p) size = Inc (W# w) <$> readback p size
readbackNeu (NSeq p q) size = Seq <$> readback p size <*> readback q size

-- * HOAS Kit

newtype TermBuilder a = TermBuilder { runTermBuilder :: Int -> a }
  deriving (Functor, Applicative, Monad)

{-# INLINE closed #-}
closed :: TermBuilder Term -> Term
closed t = runTermBuilder t 0

{-# INLINE scope #-}
scope :: (TermBuilder Term -> TermBuilder r) -> TermBuilder r
scope k = TermBuilder \n ->
  let t = TermBuilder \n' -> Var (Idx (n' - n - 1))
  in runTermBuilder (k t) (n + 1)

{-# INLINE lam #-}
lam :: (TermBuilder Term -> TermBuilder Term) -> TermBuilder Term
lam k = Lam <$> scope k

{-# INLINE app #-}
app :: TermBuilder Term -> TermBuilder Term -> TermBuilder Term
app = liftA2 App

{-# INLINE seq_ #-}
seq_ :: TermBuilder Term -> TermBuilder Term -> TermBuilder Term
seq_ = liftA2 Seq

{-# INLINE app' #-}
app' :: TermBuilder Term -> TermBuilder Term -> TermBuilder Term
app' = \f x -> seq_ x (app f x)

{-# INLINE pair #-}
pair :: TermBuilder Term -> TermBuilder Term -> TermBuilder Term
pair = liftA2 Pair

{-# INLINE fst_ #-}
fst_ :: TermBuilder Term -> TermBuilder Term
fst_ = fmap Fst

{-# INLINE snd_ #-}
snd_ :: TermBuilder Term -> TermBuilder Term
snd_ = fmap Snd

{-# INLINE zero #-}
zero :: TermBuilder Term
zero = pure (Word 0)

{-# INLINE inc #-}
inc :: Word -> TermBuilder Term -> TermBuilder Term
inc = \w -> fmap (Inc w)

{-# INLINE succ #-}
succ :: TermBuilder Term -> TermBuilder Term
succ = inc 1

-- | Create a church numeral.
{-# INLINE churchT #-}
churchT :: Word -> Term
churchT = \n -> closed $ lam \s -> lam \z -> iter (app' s) z n

-- | Read back a church numeral to a number.
{-# INLINE unChurchT #-}
unChurchT :: Term
unChurchT = closed $ lam \x -> x `app` lam succ `app` zero

-- | Addition of church numerals.
{-# INLINE addT #-}
addT :: Term
addT = closed $ lam \x -> lam \y -> lam \s -> lam \z -> x `app` s `app` (y `app` s `app` z)

main :: IO ()
main = do
  setUserEra 1
  traceMarkerIO "term"
  tm <- evaluate (unChurchT `App` (addT `App` churchT 10000000 `App` churchT 10000000))
  traceMarkerIO "interpreter"

  setUserEra 2
  p <- stToIO (stg tm Nil SNil)
  setUserEra 0

  print =<< stToIO (readback p 0)

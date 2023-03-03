{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
module Main where

--------------------------------------------------------------------------------

import Data.Map (Map)
import qualified Data.Map.Strict as M
import Data.List ((\\))
import Control.Monad.State (MonadState, StateT(StateT))
import Control.Monad.Reader (MonadReader (..), ReaderT(ReaderT))
import Control.Monad.Except (MonadError, ExceptT(..))
import Control.Monad.Trans.Writer.Lazy (WriterT (..))
import Control.Monad.Identity (Identity)
import Control.Monad.RWS.Class (MonadWriter (..))

--------------------------------------------------------------------------------

data Term = Var String
          | Abs String Type Term
          | App Term Term
          | Unit
          | T
          | F
          | If Term Term Term
          | Anno Term Type
  deriving Show

data Type = Type :-> Type | VarT String | UnitT | BoolT 
  deriving (Show, Eq)

data Scheme = Forall [String] Type
  deriving (Show, Eq)

newtype Gamma = Gamma (Map String Scheme)
    
extend :: Gamma -> (String, Scheme) -> Gamma
extend (Gamma env) (x, s) = Gamma $ Map.insert x s env

data TypeErr = TypeError deriving (Show, Eq)

type Constraint = (Type, Type)

newtype InferState = InferState { count :: Int }

newtype RWST r w s e m a  = RWST { runInfer :: r -> s -> ExceptT e m ((a, s), w) }
  deriving (Functor, Applicative, Monad, MonadReader r, MonadState s, MonadError e, MonadWriter w) via (ReaderT r (StateT s (WriterT w (ExceptT e m))))

type Infer a = RWST Gamma [Constraint] InferState TypeErr Identity a

-- | Unify two types
uni :: Type -> Type -> Infer ()
uni t1 t2 = tell [(t1, t2)]

-- | Extend type environment
inEnv :: (String, Scheme) -> Infer a -> Infer a
inEnv (x, sc) m = do
  let scope e = remove e x `extend` (x, sc)
  local scope m

main :: IO ()
main = print "hi"

{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Main where

--------------------------------------------------------------------------------

import Control.Monad.Except (ExceptT, MonadError (..), runExceptT)
import Control.Monad.Reader (MonadReader (..), Reader, runReader)
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

newtype Env = Env {getEnv :: SnocList Type}
  deriving stock (Show, Eq, Ord)

initEnv :: Env
initEnv = Env Nil

extendEnv :: Type -> Env -> Env
extendEnv ty (Env env) = Env (Snoc env ty)

resolveVar :: Env -> Ix -> Maybe Type
resolveVar ctx (Ix ix) = nth (getEnv ctx) ix

--------------------------------------------------------------------------------
-- Typechecker

data Error
  = TypeError String
  | OutOfScopeError Ix
  deriving (Show)

newtype TypecheckM a = TypecheckM {getTypecheckM :: ExceptT Error (Reader Env) a}
  deriving (Functor, Applicative, Monad, MonadReader Env, MonadError Error)

runTypecheckM :: Env -> TypecheckM a -> Either Error a
runTypecheckM env = flip runReader env . runExceptT . getTypecheckM

synth :: Term -> TypecheckM Type
synth = \case
  Var ix -> varTactic ix
  Ap tm1 tm2 -> apTactic tm1 tm2
  Anno ty tm -> check ty tm
  Unit -> pure UnitTy
  tm -> throwError $ TypeError $ "Cannot synthesize type for " <> show tm

check :: Type -> Term -> TypecheckM Type
check (FuncTy ty1 ty2) (Lam _bndr tm) = lamTactic ty1 ty2 tm
check ty tm =
  synth tm >>= \case
    ty2 | ty == ty2 -> pure ty
    ty2 -> throwError $ TypeError $ "Expected: " <> show ty <> ", but got: " <> show ty2

varTactic :: Ix -> TypecheckM Type
varTactic ix = do
  ctx <- ask
  maybe (throwError $ OutOfScopeError ix) pure $ resolveVar ctx ix

lamTactic :: Type -> Type -> Term -> TypecheckM Type
lamTactic ty1 ty2 body = do
  _ <- local (extendEnv ty1) $ check ty2 body
  pure $ FuncTy ty1 ty2

apTactic :: Term -> Term -> TypecheckM Type
apTactic tm1 tm2 =
  synth tm1 >>= \case
    FuncTy ty1 ty2 -> do
      _ <- check ty1 tm2
      pure ty2
    ty -> throwError $ TypeError $ "Expected a function type but got " <> show ty

--------------------------------------------------------------------------------
-- Evaluator

newtype EvalM a = EvalM {getEvalM :: Reader (SnocList Value) a}
  deriving (Functor, Applicative, Monad, MonadReader (SnocList Value))

runEvalM :: SnocList Value -> EvalM a -> a
runEvalM env = flip runReader env . getEvalM

eval :: Term -> EvalM Value
eval = \case
  Var (Ix ix) -> do
    env <- ask
    maybe (error "internal error") pure $ nth env ix
  Lam bndr body -> do
    env <- ask
    pure $ VLam bndr (Closure env body)
  Ap tm1 tm2 -> do
    fun <- eval tm1
    arg <- eval tm2
    doApply fun arg
  Pair tm1 tm2 -> do
    tm1' <- eval tm1
    tm2' <- eval tm2
    pure $ VPair tm1' tm2'
  Fst tm -> eval tm >>= doFst
  Snd tm -> eval tm >>= doSnd
  Anno _ty tm -> eval tm
  Unit -> pure VUnit

doApply :: Value -> Value -> EvalM Value
doApply (VLam _ clo) arg = instantiateClosure clo arg
doApply _ _ = error "impossible case in doApply"

doFst :: Value -> EvalM Value
doFst (VPair a _b) = pure a
doFst _ = error "impossible case in doFst"

doSnd :: Value -> EvalM Value
doSnd (VPair _a b) = pure b
doSnd _ = error "impossible case in doSnd"

instantiateClosure :: Closure -> Value -> EvalM Value
instantiateClosure (Closure env body) v = local (const $ Snoc env v) $ eval body

--------------------------------------------------------------------------------
-- Main

run :: Term -> Either Error Value
run term =
  runEvalM Nil . eval . const term <$> runTypecheckM initEnv (synth term)

main :: IO ()
main =
  case run idenT of
    Left err -> print err
    Right val -> print val

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

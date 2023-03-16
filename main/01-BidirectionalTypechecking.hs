{-# LANGUAGE DerivingVia #-}

module Main where

--------------------------------------------------------------------------------

import Control.Monad.Except (MonadError (..))
import Control.Monad.Identity
import Control.Monad.Reader (MonadReader (..))
import Control.Monad.Trans.Except (ExceptT (..))
import Control.Monad.Trans.Reader (Reader, ReaderT (..))
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

newtype TypecheckM a = TypecheckM {runTypecheckM :: Env -> Either Error a}
  deriving
    (Functor, Applicative, Monad, MonadReader Env, MonadError Error)
    via ExceptT Error (Reader Env)

synth :: Term -> TypecheckM Type
synth = \case
  Var ix -> varTactic ix
  Ap tm1 tm2 -> apTactic tm1 tm2
  Anno ty tm -> check ty tm
  Pair tm1 tm2 -> pairTactic tm1 tm2
  Fst tm -> fstTactic tm
  Snd tm -> sndTactic tm
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

-- | Pair Introduction Tactic
pairTactic :: Term -> Term -> TypecheckM Type
pairTactic tm1 tm2 = do
  ty1 <- synth tm1
  ty2 <- synth tm2
  pure $ PairTy ty1 ty2

-- | Pair Fst Elimination Tactic
fstTactic :: Term -> TypecheckM Type
fstTactic tm =
  synth tm >>= \case
    PairTy ty1 _ty2 -> pure ty1
    ty -> throwError $ TypeError $ "Expected a Pair but got " <> show ty
  
-- | Pair Snd Elimination Tactic
sndTactic :: Term -> TypecheckM Type
sndTactic tm =
  synth tm >>= \case
    PairTy _ty1 ty2 -> pure ty2
    ty -> throwError $ TypeError $ "Expected a Pair but got " <> show ty

--------------------------------------------------------------------------------
-- Evaluator

newtype EvalM a = EvalM {runEvalM :: SnocList Value -> a}
  deriving
    (Functor, Applicative, Monad, MonadReader (SnocList Value))
    via Reader (SnocList Value)

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
  flip runEvalM Nil . eval . const term <$> runTypecheckM (synth term) initEnv

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

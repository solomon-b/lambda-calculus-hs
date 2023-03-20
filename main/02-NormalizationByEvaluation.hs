{-# LANGUAGE DerivingVia #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

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
  = VNeutral Type Neutral
  | VLam Name Closure
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

initLevel :: Lvl
initLevel = Lvl 0

incLevel :: Lvl -> Lvl
incLevel (Lvl n) = Lvl (1 + n)

newtype Name = Name {getName :: String}
  deriving newtype (Show, Eq, Ord, IsString)

data Neutral = Neutral {head :: Head, spine :: SnocList Frame}
  deriving stock (Show, Eq, Ord)

newtype Head
  = VVar Lvl
  deriving (Show, Eq, Ord)

data Frame
  = VApp Type Value
  | VFst
  | VSnd
  deriving stock (Show, Eq, Ord)

pushFrame :: Neutral -> Frame -> Neutral
pushFrame Neutral {..} frame = Neutral {head = head, spine = Snoc spine frame}

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

newtype Check = Check {runCheck :: Type -> TypecheckM ()}

newtype Synth = Synth {runSynth :: TypecheckM Type}

synth :: Term -> Synth
synth = \case
  Var bndr -> varTactic bndr
  Ap tm1 tm2 -> applyTactic (synth tm1) (check tm2)
  Fst tm -> fstTactic (synth tm)
  Snd tm -> sndTactic (synth tm)
  Anno ty tm -> annoTactic ty (check tm)
  tm -> Synth $ throwError $ TypeError $ "Cannot synthesize type for " <> show tm

check :: Term -> Check
check (Lam _ body) = lamTactic (check body)
check Unit = unitTactic
check (Pair tm1 tm2) = pairTactic (check tm1) (check tm2)
check tm = subTactic (synth tm)

-- | Var Tactic
--
-- (x : A) ∈ Γ
-- ─────────── Var⇒
--  Γ ⊢ x ⇒ A
varTactic :: Ix -> Synth
varTactic ix = Synth $ do
  ctx <- ask
  maybe (throwError $ OutOfScopeError ix) pure $ resolveVar ctx ix

-- | Sub Tactic
--
-- Γ ⊢ e ⇒ A  A ≡ B
-- ──────────────── Sub⇐
--    Γ ⊢ e ⇐ B
subTactic :: Synth -> Check
subTactic (Synth synth') = Check $ \ty1 -> do
  ty2 <- synth'
  if ty2 == ty1
    then pure ()
    else throwError $ TypeError $ "Expected: " <> show ty1 <> ", but got: " <> show ty2

-- | Anno Tactic
--
--    Γ ⊢ e ⇐ A
-- ─────────────── Anno⇒
-- Γ ⊢ (e : A) ⇒ A
annoTactic :: Type -> Check -> Synth
annoTactic ty (Check checkAnno) = Synth $ do
  checkAnno ty
  pure ty

-- | Unit Introduction Tactic
--
-- ───────────── Unit⇐
-- Γ ⊢ () ⇐ Unit
unitTactic :: Check
unitTactic = Check $ \case
  UnitTy -> pure ()
  ty -> throwError $ TypeError $ "Expected Unit type but got: " <> show ty

-- | Lambda Introduction Tactic
--
--  Γ, x : A₁ ⊢ e ⇐ A₂
-- ──────────────────── LamIntro⇐
-- Γ ⊢ (λx.e) ⇐ A₁ → A₂
lamTactic :: Check -> Check
lamTactic (Check bodyTac) = Check $ \case
  a `FuncTy` b -> do
    local (extendEnv a) $ bodyTac b
    pure ()
  _ -> throwError $ TypeError "Tried to introduce a lambda at a non-function type"

-- | Lambda Elination Tactic
--
-- Γ ⊢ e₁ ⇒ A → B  Γ ⊢ e₂ ⇐ A
-- ────────────────────────── LamElim⇐
--       Γ ⊢ e₁ e₂ ⇒ B
applyTactic :: Synth -> Check -> Synth
applyTactic (Synth funcTac) (Check argTac) =
  Synth $
    funcTac >>= \case
      (a `FuncTy` b) -> do
        argTac a
        pure b
      ty -> throwError $ TypeError $ "Expected a function type but got " <> show ty

-- | Pair Introduction Tactic
--
-- Γ ⊢ a ⇐ A   Γ ⊢ b ⇐ B
-- ───────────────────── Pair⇐
--  Γ ⊢ (a , b) ⇐ A × B
pairTactic :: Check -> Check -> Check
pairTactic (Check checkFst) (Check checkSnd) = Check $ \case
  PairTy a b -> do
    checkFst a
    checkSnd b
    pure ()
  ty -> throwError $ TypeError $ "Expected a Pair but got " <> show ty

-- | Pair Fst Elimination Tactic
--
-- Γ ⊢ (t₁ , t₂) ⇒ A × B
-- ───────────────────── Fst⇒
--       Γ ⊢ t₁ ⇒ A
fstTactic :: Synth -> Synth
fstTactic (Synth synthPair) =
  Synth $
    synthPair >>= \case
      PairTy ty1 _ty2 -> pure ty1
      ty -> throwError $ TypeError $ "Expected a Pair but got " <> show ty

-- | Pair Snd Elimination Tactic
--
-- Γ ⊢ (t₁ , t₂) ⇒ A × B
-- ───────────────────── Snd⇒
--       Γ ⊢ t₂ ⇒ A
sndTactic :: Synth -> Synth
sndTactic (Synth synthPair) =
  Synth $
    synthPair >>= \case
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
doApply (VNeutral (FuncTy ty1 ty2) neu) arg = pure $ VNeutral ty2 (pushFrame neu (VApp ty1 arg))
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
-- Quoting

quote :: Lvl -> Type -> Value -> EvalM Term
quote l (FuncTy ty1 ty2) (VLam bndr clo@(Closure _env _body)) = do
  body <- bindVar ty1 l $ \v l' -> do
    clo <- instantiateClosure clo v
    quote l' ty2 clo
  pure $ Lam bndr body
quote l (FuncTy ty1 ty2) f = do
  body <- bindVar ty1 l $ \v l' ->
    doApply f v >>= quote l' ty2
  pure $ Lam "_" body
quote l (PairTy ty1 ty2) (VPair tm1 tm2) = do
  tm1' <- quote l ty1 tm1
  tm2' <- quote l ty2 tm2
  pure $ Pair tm1' tm2'
quote l _ (VNeutral _ neu) = quoteNeutral l neu
quote _ _ VUnit = pure Unit
quote _ _ _ = error "impossible case in quote"

bindVar :: Type -> Lvl -> (Value -> Lvl -> a) -> a
bindVar ty lvl f =
  let v = VNeutral ty $ Neutral (VVar lvl) Nil
   in f v $ incLevel lvl

quoteLevel :: Lvl -> Lvl -> Ix
quoteLevel (Lvl l) (Lvl x) = Ix (l - (x + 1))

quoteNeutral :: Lvl -> Neutral -> EvalM Term
quoteNeutral l Neutral {..} = foldM (quoteFrame l) (quoteHead l head) spine

quoteHead :: Lvl -> Head -> Term
quoteHead l (VVar x) = Var $ quoteLevel l x

quoteFrame :: Lvl -> Term -> Frame -> EvalM Term
quoteFrame l tm = \case
  VApp ty arg -> Ap tm <$> quote l ty arg
  VFst -> pure $ Fst tm
  VSnd -> pure $ Snd tm

--------------------------------------------------------------------------------
-- Main

run :: Term -> Either Error Term
run term = do
  type' <- runTypecheckM (runSynth $ synth term) initEnv
  pure $ flip runEvalM Nil $ (eval >=> quote initLevel type') term

main :: IO ()
main =
  case run (Ap idenT Unit) of
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

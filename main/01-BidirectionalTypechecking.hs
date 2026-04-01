{-# LANGUAGE DerivingVia #-}

-- | Bidirectional Typechecking.
--
-- Adds a typechecker split into two mutually recursive judgements: 'Synth'
-- (type synthesis, where the term tells us its type) and 'Check' (type
-- checking, where we push an expected type into the term). Lambdas, pairs,
-- and unit are checked; variables, application, projections, and annotations
-- are synthesized. The 'subTactic' bridges the two: a synthesizable term can
-- be used in a checked position if the types match.
module Main where

--------------------------------------------------------------------------------

import Control.Monad.Except (MonadError (..))
import Control.Monad.Identity
import Control.Monad.Reader (MonadReader (..))
import Control.Monad.Trans.Except (ExceptT (..))
import Control.Monad.Trans.Reader (Reader, ReaderT (..))
import Data.String
import TestHarness (RunResult (..), runTest, runTestErr, section)

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

run :: Term -> Either (Error, ()) (RunResult () Type Value, ())
run term =
  case runTypecheckM (runSynth $ synth term) initEnv of
    Left err -> Left (err, ())
    Right type' -> do
      let value = flip runEvalM Nil $ eval term
      pure (RunResult () type' value, ())

main :: IO ()
main = do
  let test = runTest run
      testErr = runTestErr run

  putStrLn "=== Bidirectional Typechecking ==="
  putStrLn ""

  -- Synth: Anno pushes type info in, enabling check of the body
  section "Anno (Synth)"
  test
    "() : Unit"
    (Anno UnitTy Unit)
  test
    "\\x. x : Unit -> Unit"
    (Anno (UnitTy `FuncTy` UnitTy) (Lam "x" (Var (Ix 0))))
  test
    "((), ()) : Unit * Unit"
    (Anno (PairTy UnitTy UnitTy) (Pair Unit Unit))
  putStrLn ""

  -- Synth: Var
  section "Var (Synth)"
  test
    "(\\x. x : U -> U) () — Var 0 synthesizes from context"
    ( Ap
        (Anno (UnitTy `FuncTy` UnitTy) (Lam "x" (Var (Ix 0))))
        Unit
    )
  test
    "(\\x. \\y. x : U -> U -> U) () () — Var 1 reaches outer binder"
    ( Ap
        ( Ap
            ( Anno
                (UnitTy `FuncTy` (UnitTy `FuncTy` UnitTy))
                (Lam "x" (Lam "_" (Var (Ix 1))))
            )
            Unit
        )
        Unit
    )
  putStrLn ""

  -- Synth: Ap
  section "Application (Synth)"
  test
    "(\\f. \\x. f x : (U->U) -> U -> U) (\\x. x) () ==> ()"
    ( Ap
        ( Ap
            ( Anno
                ((UnitTy `FuncTy` UnitTy) `FuncTy` (UnitTy `FuncTy` UnitTy))
                (Lam "f" (Lam "x" (Ap (Var (Ix 1)) (Var (Ix 0)))))
            )
            (Anno (UnitTy `FuncTy` UnitTy) (Lam "x" (Var (Ix 0))))
        )
        Unit
    )
  putStrLn ""

  -- Synth: Fst / Snd
  section "Fst / Snd (Synth)"
  test
    "fst ((), ()) ==> ()"
    (Fst (Anno (PairTy UnitTy UnitTy) (Pair Unit Unit)))
  test
    "snd ((), ()) ==> ()"
    (Snd (Anno (PairTy UnitTy UnitTy) (Pair Unit Unit)))
  putStrLn ""

  -- Check: Lam — checks body against return type
  section "Lambda (Check)"
  test
    "\\x. x checked at U -> U"
    (Anno (UnitTy `FuncTy` UnitTy) (Lam "x" (Var (Ix 0))))
  test
    "\\x. \\y. x checked at U -> U -> U"
    ( Anno
        (UnitTy `FuncTy` (UnitTy `FuncTy` UnitTy))
        (Lam "x" (Lam "y" (Var (Ix 1))))
    )
  test
    "\\f. \\x. f x checked at (U->U) -> U -> U"
    ( Anno
        ((UnitTy `FuncTy` UnitTy) `FuncTy` (UnitTy `FuncTy` UnitTy))
        (Lam "f" (Lam "x" (Ap (Var (Ix 1)) (Var (Ix 0)))))
    )
  putStrLn ""

  -- Check: Pair — checks each component
  section "Pair (Check)"
  test
    "nested pair (((), ()), ()) : (U * U) * U"
    ( Anno
        (PairTy (PairTy UnitTy UnitTy) UnitTy)
        (Pair (Pair Unit Unit) Unit)
    )
  putStrLn ""

  -- Sub tactic: synth term used in check position
  section "Sub Tactic (Synth in Check Position)"
  test
    "fst used in check position: \\x. fst x checked at (U*U) -> U"
    ( Anno
        (PairTy UnitTy UnitTy `FuncTy` UnitTy)
        (Lam "x" (Fst (Var (Ix 0))))
    )
  test
    "anno in check position: (\\x. x : U -> U) inside anno"
    ( Anno
        (UnitTy `FuncTy` UnitTy)
        (Anno (UnitTy `FuncTy` UnitTy) (Lam "x" (Var (Ix 0))))
    )
  putStrLn ""

  -- Error cases
  section "Error Cases (expected failures)"
  testErr
    "Cannot synthesize lambda"
    (Lam "x" (Var (Ix 0)))
  testErr
    "Cannot synthesize pair"
    (Pair Unit Unit)
  testErr
    "Cannot synthesize unit"
    Unit
  testErr
    "Out of scope variable (Ix 0 in empty context)"
    (Anno UnitTy (Var (Ix 0)))
  testErr
    "Lambda checked at non-function type"
    (Anno UnitTy (Lam "x" (Var (Ix 0))))
  testErr
    "Unit checked at function type"
    (Anno (UnitTy `FuncTy` UnitTy) Unit)
  testErr
    "Apply non-function"
    (Ap (Anno UnitTy Unit) Unit)
  testErr
    "Pair checked at non-pair type"
    (Anno UnitTy (Pair Unit Unit))
  testErr
    "Type mismatch via sub tactic"
    ( Anno
        (PairTy UnitTy UnitTy)
        (Anno UnitTy Unit)
    )

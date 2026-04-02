{-# LANGUAGE DerivingVia #-}

-- | Bidirectional Typechecking.
--
-- Adds a typechecker split into two mutually recursive judgements:
--
--   - 'Synth': type synthesis, where the term tells us its type.
--   - 'Check': type checking, where we push an expected type into the term.
--
-- Lambdas, pairs, and unit are checked; variables, application, projections,
-- and annotations are synthesized. The 'subTactic' bridges the two: a
-- synthesizable term can be used in a checked position if the types match.
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

-- | A list that grows on the right. We use this as our environment
-- representation because it matches the structure of de Bruijn indices: the
-- most recently bound variable is at the end (index 0), and older bindings are
-- further left (higher indices).
--
-- A regular list would work too, but snoc lists make the correspondence between
-- binding order and index explicit.
data SnocList a
  = Snoc (SnocList a) a
  | Nil
  deriving (Show, Eq, Ord, Functor, Foldable)

-- | Look up a value by de Bruijn index, counting from the right (most recent
-- binding).
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
-- Syntax
--
-- Our language has two representations:
--
--   - 'Term' - what the programmer writes.
--   - 'Value' - what evaluation produces.
--
-- A 'Lam' in the syntax becomes a 'VLam' closure that captures its environment,
-- deferring substitution until thefunction is applied.

-- | The abstract syntax tree of our language.
--
-- Variables use de Bruijn indices ('Ix') rather than names, which makes
-- alpha-equivalence trivial (syntactic equality) at the cost of human
-- readability.
data Term
  = -- | A variable reference by de Bruijn index. @x@
    Var Ix
  | -- | Lambda abstraction. @\x. body@
    Lam Name Term
  | -- | Function application. @f x@
    Ap Term Term
  | -- | Pair introduction. @(a, b)@
    Pair Term Term
  | -- | First projection of a pair. @fst p@
    Fst Term
  | -- | Second projection of a pair. @snd p@
    Snd Term
  | -- | The unit value. @()@
    Unit
  | -- | A term with a type annotation that we ignore during evaluation. @(t : A)@
    Anno Type Term
  deriving stock (Show, Eq, Ord)

-- | The type language.
--
-- At this point we have no type inference, so every lambda needs an annotation
-- (via 'Anno') to tell us its type. We have function types, pair types, and the
-- unit type.
data Type
  = -- | Function type. @A -> B@.
    FuncTy Type Type
  | -- | Pair type. @A * B@.
    PairTy Type Type
  | -- | Unit type. @Unit@.
    UnitTy
  deriving stock (Show, Eq, Ord)

-- | The result of evaluation.
--
-- The key difference from 'Term' is that lambdas become 'VLam' closures that
-- pair the function body with the environment it was defined in.
--
-- This is how we avoid substitution, instead of replacing variables in the
-- body, we record what they should evaluate to in the closure's environment and
-- look them up at use sites.
data Value
  = -- | A closure: the lambda body paired with its defining environment.
    -- Application triggers beta reduction by extending this environment.
    VLam Name Closure
  | -- | A fully evaluated pair of values.
    VPair Value Value
  | -- | The unit value.
    VUnit
  deriving stock (Show, Eq, Ord)

-- | De Bruijn Indices.
--
-- 'Ix' is used to reference lambda-bound terms with respect to α-conversion.
-- The index @n@ represents the value bound by the @n@th lambda counting outward
-- from the site of the index.
--
-- λ.λ.λ.2
-- ^-----^
newtype Ix
  = Ix Int
  deriving newtype (Show, Eq, Ord)

newtype Name = Name {getName :: String}
  deriving newtype (Show, Eq, Ord, IsString)

-- | A closure pairs a function body with the environment it was defined in.
-- When we evaluate @λx. body@ in environment @env@, we don't substitute into
-- @body@, we store @(env, body)@ as a 'Closure'. Later, when the function is
-- applied to an argument @v@, we evaluate @body@ in @Snoc env v@: the original
-- environment extended with the argument.
--
-- This "substitution by environment extension" is the core trick that makes
-- evaluation efficient. It turns substitution (a traversal of the entire term)
-- into a constant-time environment push.
data Closure = Closure {env :: SnocList Value, body :: Term}
  deriving stock (Show, Eq, Ord)

--------------------------------------------------------------------------------
-- Environment
--
-- The typechecker environment maps de Bruijn indices to their types. This is
-- separate from the evaluator's environment (which maps indices to values). the
-- typechecker only needs to know what type each variable has, not what value it
-- holds.

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
--
-- The typechecker is split into two mutually recursive judgements:
--
--   - 'Synth': The term tells us its type.
--   - 'Check': We push an expected type into the term.
--
-- Terms that introduce a type former (lambdas, pairs, unit) are checked. Terms
-- that eliminate one (application, projection) or carry an annotation are
-- synthesized. The 'subTactic' bridges the two directions.

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
-- Look up a variable's type in the context by its de Bruijn index. This is a
-- synth rule, the context tells us the type, we don't need it pushed in.
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
-- The bridge between synth and check. Synthesize a type for the term, then
-- verify it matches the expected type. This is how a synthesizable term (like a
-- variable or annotation) can appear in a checked position. Every term that
-- doesn't have its own check rule falls through to this.
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
-- The annotation provides a type, switching from synth to check mode. We check
-- the body against the annotated type, then synthesize that type as the result.
-- This is the primary way to give a type to check-only terms like lambdas.
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
-- Unit is a check rule, we verify the expected type is 'UnitTy'. There's
-- nothing to synthesize since @()@ doesn't carry type information.
--
-- ───────────── Unit⇐
-- Γ ⊢ () ⇐ Unit
unitTactic :: Check
unitTactic = Check $ \case
  UnitTy -> pure ()
  ty -> throwError $ TypeError $ "Expected Unit type but got: " <> show ty

-- | Lambda Introduction Tactic
--
-- A lambda is checked against a function type. The expected type @A₁ → A₂@
-- tells us what type the parameter has (@A₁@), so we extend the context and
-- check the body against the return type (@A₂@). This is why lambdas can't
-- synthesize. Without the expected function type, we wouldn't know @A₁@.
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

-- | Lambda Elimination Tactic
--
-- Application is a synth rule. Synthesize the function's type to get @A → B@,
-- then check the argument against @A@, and return @B@. The function type tells
-- us what to check the argument against. Information flows from the function to
-- the argument.
--
-- Γ ⊢ e₁ ⇒ A → B  Γ ⊢ e₂ ⇐ A
-- ────────────────────────── LamElim⇒
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
-- Like lambdas, pairs are checked. the expected pair type @A × B@ tells us what
-- to check each component against.
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
-- Projection is a synth rule. Synthesize the pair's type to learn what the
-- components are, then return the appropriate one.
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
-- Same as fst, but returns the second component.
--
-- Γ ⊢ (t₁ , t₂) ⇒ A × B
-- ───────────────────── Snd⇒
--       Γ ⊢ t₂ ⇒ B
sndTactic :: Synth -> Synth
sndTactic (Synth synthPair) =
  Synth $
    synthPair >>= \case
      PairTy _ty1 ty2 -> pure ty2
      ty -> throwError $ TypeError $ "Expected a Pair but got " <> show ty

--------------------------------------------------------------------------------
-- Evaluator
--
-- Evaluation maps 'Term' to 'Value' under an environment. The interesting cases
-- are:
--
-- - 'Var': look up the value in the environment by de Bruijn index.
-- - 'Lam': capture the current environment in a closure (don't evaluate the
--          body yet, since we don't know the argument).
-- - 'Ap': evaluate both sides, then apply. This is where beta reduction
--         happens, by instantiating the closure with the argument.

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

-- | Apply a function value to an argument. This is beta reduction: @(λx. body)
-- arg@ becomes @body@ evaluated in the closure's captured environment extended
-- with @arg@.
doApply :: Value -> Value -> EvalM Value
doApply (VLam _ clo) arg = instantiateClosure clo arg
doApply _ _ = error "impossible case in doApply"

doFst :: Value -> EvalM Value
doFst (VPair a _b) = pure a
doFst _ = error "impossible case in doFst"

doSnd :: Value -> EvalM Value
doSnd (VPair _a b) = pure b
doSnd _ = error "impossible case in doSnd"

-- | Instantiate a closure by extending its captured environment with the
-- argument value, then evaluating the body.
--
-- This is the key operation: substitution is replaced by a constant-time
-- 'Snoc', and the actual lookup happens lazily when we hit a 'Var' during
-- evaluation of the body.
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

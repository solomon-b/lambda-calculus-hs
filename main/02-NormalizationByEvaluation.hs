{-# LANGUAGE DerivingVia #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- | Normalization by Evaluation (NbE).
--
-- Adds the ability to normalize terms by evaluating them into a semantic domain
-- ('Value') and quoting back to syntax.
--
-- Neutral terms ('VNeutral') represent stuck computations, variables that can't
-- reduce further.
--
-- Quoting is type-directed: at function types it eta-expands, ensuring every
-- normal form is fully eta-long. The result is a normalizer that decides
-- beta-eta equality for the simply typed lambda calculus.
module Main where

--------------------------------------------------------------------------------

import Control.Monad (foldM, (>=>))
import Control.Monad.Except (MonadError (..))
import Control.Monad.Identity
import Control.Monad.Reader (MonadReader (..))
import Control.Monad.Trans.Except (ExceptT (..))
import Control.Monad.Trans.Reader (Reader, ReaderT (..))
import Data.String
import PrettyTerm (Prec, appPrec, arrowPrec, arrowSym, atomPrec, lamPrec, lambdaSym, parensIf)
import PrettyTerm qualified as PP
import TestHarness (RunResult (..), runTest, runTestErr, section)
import Utils (SnocList (..), nth)

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

-- In this module 'Value' gains a 'VNeutral' for stuck computations. This
-- represents a variable applied to arguments that can't reduce. Neutrals are
-- what make NbE work. They let us evaluate under binders by introducing fresh
-- variables that block reduction, then quote the result back to syntax.

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

prettyTerm :: Prec -> Term -> PP.Doc ann
prettyTerm _ (Var (Ix n)) = "#" <> PP.pretty n
prettyTerm p (Lam n body) =
  parensIf (p > lamPrec) $
    lambdaSym <> PP.pretty (getName n) <> "." PP.<+> prettyTerm lamPrec body
prettyTerm p (Ap f x) =
  parensIf (p > appPrec) $
    prettyTerm appPrec f PP.<+> prettyTerm atomPrec x
prettyTerm _ (Pair a b) =
  PP.tupled [prettyTerm lamPrec a, prettyTerm lamPrec b]
prettyTerm p (Fst e) =
  parensIf (p > appPrec) $
    "fst" PP.<+> prettyTerm atomPrec e
prettyTerm p (Snd e) =
  parensIf (p > appPrec) $
    "snd" PP.<+> prettyTerm atomPrec e
prettyTerm _ Unit = "()"
prettyTerm p (Anno ty e) =
  parensIf (p > lamPrec) $
    prettyTerm (lamPrec + 1) e PP.<+> ":" PP.<+> prettyType lamPrec ty

instance PP.Pretty Term where
  pretty = prettyTerm lamPrec

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

prettyType :: Prec -> Type -> PP.Doc ann
prettyType p (FuncTy a b) =
  parensIf (p > arrowPrec) $
    prettyType (arrowPrec + 1) a PP.<+> arrowSym PP.<+> prettyType arrowPrec b
prettyType p (PairTy a b) =
  parensIf (p > arrowPrec) $
    prettyType (arrowPrec + 1) a PP.<+> "*" PP.<+> prettyType arrowPrec b
prettyType _ UnitTy = "Unit"

instance PP.Pretty Type where
  pretty = prettyType lamPrec

-- | The result of evaluation.
--
-- The key difference from 'Term' is that lambdas become 'VLam' closures that
-- pair the function body with the environment it was defined in.
--
-- This is how we avoid substitution, instead of replacing variables in the
-- body, we record what they should evaluate to in the closure's environment and
-- look them up at use sites.
data Value
  = -- | A stuck computation, a variable applied to arguments that can't reduce.
    -- The 'Type' annotation is needed so quoting knows how to eta-expand (e.g.,
    -- a neutral at function type gets wrapped in a lambda).
    VNeutral Type Neutral
  | -- | A closure: the lambda body paired with its defining environment.
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

-- | De Bruijn Levels.
--
-- Similar to de Bruijn indices but counting inward from the outermost lambda.
--
-- λ.λ.λ.0
-- ^-----^
--
-- Levels eliminate the need to reindex free variables when weakening the
-- context. This is useful in our 'Value' representation of lambdas where we
-- have a 'Closure' holding a stack of free variables.
newtype Lvl
  = Lvl Int
  deriving newtype (Show, Eq, Ord)

initLevel :: Lvl
initLevel = Lvl 0

incLevel :: Lvl -> Lvl
incLevel (Lvl n) = Lvl (1 + n)

newtype Name = Name {getName :: String}
  deriving newtype (Show, Eq, Ord, IsString)

-- | A neutral term is a head (a variable) applied to a spine of eliminators. We
-- can't reduce it because the head is a variable, we don't know what it is. For
-- example, @x (λy. y) ()@ is a neutral with head @x@ and spine @[VApp (λy. y),
-- VApp ()]@.
data Neutral = Neutral {head :: Head, spine :: SnocList Frame}
  deriving stock (Show, Eq, Ord)

-- | The head of a neutral is always a variable, represented as a de Bruijn
-- level (not index) so it stays stable under context extension.
newtype Head
  = VVar Lvl
  deriving (Show, Eq, Ord)

-- | A frame is a single eliminator waiting to be applied to a neutral. The
-- spine of a neutral is a sequence of these.
data Frame
  = VApp Type Value
  | VFst
  | VSnd
  deriving stock (Show, Eq, Ord)

pushFrame :: Neutral -> Frame -> Neutral
pushFrame Neutral {..} frame = Neutral {head = head, spine = Snoc spine frame}

-- | A closure pairs a function body with the environment it was defined in.
-- Instantiation extends the captured environment with the argument rather than
-- substituting. Closures also appear inside neutrals (as arguments in 'VApp'
-- frames).
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
--

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

-- | Apply a function value to an argument.
--
-- 'doApply' has two cases:
--   1. Lambda reduces (beta)
--   2. A neutral accumulates the argument onto its spine (stuck).
--
-- This is what lets us evaluate under binders. We apply a closure to a fresh
-- neutral variable, and the result is a value with neutrals wherever the
-- variable appeared.
doApply :: Value -> Value -> EvalM Value
doApply (VLam _ clo) arg = appTermClosure clo arg
doApply (VNeutral (FuncTy ty1 ty2) neu) arg = pure $ VNeutral ty2 (pushFrame neu (VApp ty1 arg))
doApply _ _ = error "impossible case in doApply"

doFst :: Value -> EvalM Value
doFst (VPair a _b) = pure a
doFst _ = error "impossible case in doFst"

doSnd :: Value -> EvalM Value
doSnd (VPair _a b) = pure b
doSnd _ = error "impossible case in doSnd"

appTermClosure :: Closure -> Value -> EvalM Value
appTermClosure (Closure env body) v = local (const $ Snoc env v) $ eval body

--------------------------------------------------------------------------------
-- Quoting
--
-- Quoting reads back a 'Value' into a 'Term' (normal form). It is
-- type-directed, the type tells us how to handle each value.
--
-- At function types quoting eta-expands, so even a neutral gets wrapped in a
-- lambda. This ensures normal forms are fully eta-long, which means two terms
-- are beta-eta equal iff their normal forms are syntactically identical.
--
-- The 'Lvl' parameter tracks how many binders we've gone under, so we can
-- convert de Bruijn levels (stable under extension) back to de Bruijn indices
-- (what syntax uses).

-- | Quote a value back to a term, producing a beta-normal eta-long form. The
-- first 'Lvl' argument tracks the current binding depth.
quote :: Lvl -> Type -> Value -> EvalM Term
quote l (FuncTy ty1 ty2) (VLam bndr clo@(Closure _env _body)) = do
  body <- bindVar ty1 l $ \v l' -> do
    clo <- appTermClosure clo v
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

-- | Create a fresh neutral variable at the current level and pass it to the
-- continuation with an incremented level. This is how we go under a binder
-- during quoting. We apply the closure to a fresh variable and quote the
-- result.
bindVar :: Type -> Lvl -> (Value -> Lvl -> a) -> a
bindVar ty lvl f =
  let v = VNeutral ty $ Neutral (VVar lvl) Nil
   in f v $ incLevel lvl

-- | Convert a de Bruijn level to a de Bruijn index given the current depth.
-- Levels count from the outermost binder, indices count from the innermost, so
-- the conversion is @index = depth - level - 1@.
quoteLevel :: Lvl -> Lvl -> Ix
quoteLevel (Lvl l) (Lvl x) = Ix (l - (x + 1))

-- | Quote a neutral by quoting the head, then folding over the spine, quoting
-- each frame and applying it.
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

run :: Term -> Either (Error, ()) (RunResult () Type Term, ())
run term =
  case runTypecheckM (runSynth $ synth term) initEnv of
    Left err -> Left (err, ())
    Right type' -> do
      let result = flip runEvalM Nil $ (eval >=> quote initLevel type') term
      pure (RunResult () type' result, ())

main :: IO ()
main = do
  let test = runTest run
      testErr = runTestErr run

  putStrLn "=== Normalization by Evaluation ==="
  putStrLn ""

  -- Beta reduction — (λx. body) arg normalizes by substitution
  section "Beta Reduction"
  test
    "(\\x. x) () ==> ()"
    ( Ap
        (Anno (UnitTy `FuncTy` UnitTy) (Lam "x" (Var (Ix 0))))
        Unit
    )
  test
    "(\\x. \\y. x) () () ==> ()"
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
  test
    "(\\f. \\x. f x) (\\x. x) () ==> ()"
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

  -- Eta expansion — λf. f at (A -> B) -> (A -> B) normalizes to λf. λx. f x
  section "Eta Expansion"
  test
    "\\f. f : (U->U) -> (U->U) normalizes to \\f. \\x. f x"
    ( Anno
        ((UnitTy `FuncTy` UnitTy) `FuncTy` (UnitTy `FuncTy` UnitTy))
        (Lam "f" (Var (Ix 0)))
    )
  test
    "\\x. x : U -> U stays as \\x. x (no expansion at base return type)"
    ( Anno
        (UnitTy `FuncTy` UnitTy)
        (Lam "x" (Var (Ix 0)))
    )
  test
    "\\f. f : ((U->U)->U) -> ((U->U)->U) eta-expands inner arg"
    ( Anno
        (((UnitTy `FuncTy` UnitTy) `FuncTy` UnitTy) `FuncTy` ((UnitTy `FuncTy` UnitTy) `FuncTy` UnitTy))
        (Lam "f" (Var (Ix 0)))
    )
  putStrLn ""

  -- Pair normalization
  section "Pair Normalization"
  test
    "((), ()) : U * U"
    (Anno (PairTy UnitTy UnitTy) (Pair Unit Unit))
  test
    "fst ((), ()) ==> ()"
    (Fst (Anno (PairTy UnitTy UnitTy) (Pair Unit Unit)))
  test
    "snd ((), ()) ==> ()"
    (Snd (Anno (PairTy UnitTy UnitTy) (Pair Unit Unit)))
  test
    "\\x. (x, x) : U -> U * U"
    ( Anno
        (UnitTy `FuncTy` PairTy UnitTy UnitTy)
        (Lam "x" (Pair (Var (Ix 0)) (Var (Ix 0))))
    )
  putStrLn ""

  -- Beta + eta combined
  section "Beta and Eta Combined"
  test
    "(\\f. f) (\\x. x) : (U->U) -> (U->U) normalizes to \\x. x"
    ( Ap
        ( Anno
            ((UnitTy `FuncTy` UnitTy) `FuncTy` (UnitTy `FuncTy` UnitTy))
            (Lam "f" (Var (Ix 0)))
        )
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
    "Apply non-function"
    (Ap (Anno UnitTy Unit) Unit)
  testErr
    "Type mismatch: pair checked at function type"
    (Anno (UnitTy `FuncTy` UnitTy) (Pair Unit Unit))

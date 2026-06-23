{-# LANGUAGE DerivingVia #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- | Typed Holes.
--
-- Adds hole support: a 'Hole' in the surface syntax can stand for any missing
-- subterm. During checking, a hole accepts whatever type is pushed into it and
-- records that type via a 'Writer' effect, producing an 'SHole' in the core IR.
-- Holes evaluate to neutral terms so they propagate through NbE without
-- crashing. The normal form still contains the hole annotated with its expected
-- type.
module Main where

--------------------------------------------------------------------------------

import Control.Monad (foldM)
import Control.Monad.Except (MonadError (..))
import Control.Monad.Identity
import Control.Monad.Reader (MonadReader (..))
import Control.Monad.Trans.Except (ExceptT (..))
import Control.Monad.Trans.Reader (Reader, ReaderT (..))
import Control.Monad.Trans.Writer.Strict (WriterT (..))
import Control.Monad.Writer.Strict (MonadWriter (..))
import Data.Foldable (find)
import Data.Maybe (fromMaybe)
import Data.String
import PrettyTerm (Prec, appPrec, arrowPrec, arrowSym, atomPrec, lamPrec, lambdaSym, parensIf)
import PrettyTerm qualified as PP
import TestHarness (RunResult (..), runTest, runTestErr, section)
import Utils (SnocList (..), nth)

--------------------------------------------------------------------------------
-- Syntax
--
-- We use a three-level representation:
--
-- 1. 'Term': surface syntax with named variables, what the programmer writes.
-- 2. 'Syntax': core IR with de Bruijn indices, produced by elaboration.
-- 3. 'Value': semantic domain with closures and neutrals, produced by evaluation.
--
-- 'Term' uses named variables ('Name') instead of de Bruijn indices. The
-- typechecker resolves names to indices during elaboration, producing 'Syntax'.
-- This means typechecking and elaboration happen in a single pass.
--
-- New in this module: 'Hole' in the surface syntax, 'SHole' in the core IR, and
-- 'VHole' as a neutral head. A hole can appear wherever a checked term is
-- expected, the typechecker records its expected type and elaboration
-- continues.

-- | Surface syntax with named variables. The programmer writes @λx. x@ and
-- elaboration resolves @x@ to the appropriate de Bruijn index.
data Term
  = -- | A variable reference by name. @x@
    Var Name
  | -- | Lambda abstraction. @\x. body@
    Lam Name Term
  | -- | Function application. @f x@
    Ap Term Term
  | -- | Let binding. @let x = t1 in t2@
    Let Name Term Term
  | -- | A term with a type annotation that we ignore during evaluation. @(t : A)@
    Anno Type Term
  | -- | A missing subterm. Can only appear in check position (where the
    -- expected type is known). In synth position it's an error.
    Hole
  | -- | Pair introduction. @(a, b)@
    Pair Term Term
  | -- | First projection of a pair. @fst p@
    Fst Term
  | -- | Second projection of a pair. @snd p@
    Snd Term
  | -- | Left injection into a sum type.
    InL Term
  | -- | Right injection into a sum type.
    InR Term
  | -- | Binary sum elimination. Binds a variable in each branch.
    Case Term (Name, Term) (Name, Term)
  | -- | Void elimination. Can produce any type from a value of type 'Void',
    -- since no such value exists.
    Absurd Term
  | -- | The unit value. @()@
    Unit
  | -- | Boolean true. @true@
    Tru
  | -- | Boolean false. @false@
    Fls
  | -- | Conditional. @if scrut then t else f@
    If Term Term Term
  deriving stock (Show, Eq, Ord)

prettyTerm :: Prec -> Term -> PP.Doc ann
prettyTerm _ (Var n) = PP.pretty (getName n)
prettyTerm p (Lam n body) =
  parensIf (p > lamPrec) $
    lambdaSym <> PP.pretty (getName n) <> "." PP.<+> prettyTerm lamPrec body
prettyTerm p (Ap f x) =
  parensIf (p > appPrec) $
    prettyTerm appPrec f PP.<+> prettyTerm atomPrec x
prettyTerm p (Let n rhs body) =
  parensIf (p > lamPrec) $
    "let"
      PP.<+> PP.pretty (getName n)
      PP.<+> "="
      PP.<+> prettyTerm lamPrec rhs
      PP.<+> "in"
      PP.<+> prettyTerm lamPrec body
prettyTerm p (Anno ty e) =
  parensIf (p > lamPrec) $
    prettyTerm (lamPrec + 1) e PP.<+> ":" PP.<+> prettyType lamPrec ty
prettyTerm _ Hole = "_"
prettyTerm _ (Pair a b) =
  PP.tupled [prettyTerm lamPrec a, prettyTerm lamPrec b]
prettyTerm p (Fst e) =
  parensIf (p > appPrec) $
    "fst" PP.<+> prettyTerm atomPrec e
prettyTerm p (Snd e) =
  parensIf (p > appPrec) $
    "snd" PP.<+> prettyTerm atomPrec e
prettyTerm _ Tru = "True"
prettyTerm _ Fls = "False"
prettyTerm p (If scrut t f) =
  parensIf (p > lamPrec) $
    "if"
      PP.<+> prettyTerm lamPrec scrut
      PP.<+> "then"
      PP.<+> prettyTerm lamPrec t
      PP.<+> "else"
      PP.<+> prettyTerm lamPrec f
prettyTerm _ Unit = "()"
prettyTerm p (Absurd e) =
  parensIf (p > appPrec) $
    "absurd" PP.<+> prettyTerm atomPrec e
prettyTerm p (InL e) =
  parensIf (p > appPrec) $
    "inl" PP.<+> prettyTerm atomPrec e
prettyTerm p (InR e) =
  parensIf (p > appPrec) $
    "inr" PP.<+> prettyTerm atomPrec e
prettyTerm p (Case scrut (ln, l) (rn, r)) =
  parensIf (p > lamPrec) $
    "case"
      PP.<+> prettyTerm lamPrec scrut
      PP.<+> "of"
      PP.<+> "inl"
      PP.<+> PP.pretty (getName ln)
      PP.<+> arrowSym
      PP.<+> prettyTerm lamPrec l
      <> ";"
        PP.<+> "inr"
        PP.<+> PP.pretty (getName rn)
        PP.<+> arrowSym
        PP.<+> prettyTerm lamPrec r

instance PP.Pretty Term where
  pretty = prettyTerm lamPrec

-- | The type language. Functions, pairs, and unit.
data Type
  = -- | Function type. @A -> B@.
    FuncTy Type Type
  | -- | Pair type. @A * B@.
    PairTy Type Type
  | -- | Binary sum: @A + B@.
    SumTy Type Type
  | -- | The empty type. No values inhabit it.
    VoidTy
  | -- | Unit type. @Unit@.
    UnitTy
  | -- | Bool Type. @Bool@.
    BoolTy
  deriving stock (Show, Eq, Ord)

prettyType :: Prec -> Type -> PP.Doc ann
prettyType p (FuncTy a b) =
  parensIf (p > arrowPrec) $
    prettyType (arrowPrec + 1) a PP.<+> arrowSym PP.<+> prettyType arrowPrec b
prettyType p (PairTy a b) =
  parensIf (p > arrowPrec) $
    prettyType (arrowPrec + 1) a PP.<+> "*" PP.<+> prettyType arrowPrec b
prettyType _ BoolTy = "Bool"
prettyType _ UnitTy = "Unit"
prettyType _ VoidTy = "Void"
prettyType p (SumTy a b) =
  parensIf (p > PP.sumPrec) $
    prettyType (PP.sumPrec + 1) a PP.<+> "+" PP.<+> prettyType PP.sumPrec b

instance PP.Pretty Type where
  pretty = prettyType lamPrec

-- | Core IR with de Bruijn indices.
--
-- This is what the evaluator operates on. Elaboration translates 'Term' into
-- 'Syntax', resolving named variables to indices and stripping away
-- annotations.
data Syntax
  = -- | A resolved variable reference by de Bruijn index.
    SVar Ix
  | -- | Lambda abstraction in core IR.
    SLam Name Syntax
  | -- | Function application in core IR.
    SAp Syntax Syntax
  | -- | A hole in the core IR, carrying the expected type. Evaluates to a
    -- neutral so it propagates through NbE.
    SHole Type
  | -- | Pair introduction in core IR.
    SPair Syntax Syntax
  | -- | First projection of a pair.
    SFst Syntax
  | -- | Second projection of a pair.
    SSnd Syntax
  | SInL Syntax
  | SInR Syntax
  | SCase Syntax Type Syntax Syntax
  | SAbsurd Type Syntax
  | -- | The unit value.
    SUnit
  | -- | Boolean true.
    STru
  | -- | Boolean false.
    SFls
  | -- | Conditional. @if scrut then t else f@.
    SIf Syntax Type Syntax Syntax
  deriving stock (Show, Eq, Ord)

-- | The result of evaluation.
--
-- The key difference from 'Syntax' is that lambdas become 'VLam' closures that
-- pair the function body with the environment it was defined in. Closures hold
-- 'Syntax' bodies, since the evaluator operates on the elaborated core IR.
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
  | -- | Left injection value.
    VInL Value
  | -- | Right injection value.
    VInR Value
  | -- | The unit value.
    VUnit
  | -- | Boolean true.
    VTru
  | -- | Boolean false.
    VFls
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
data Head
  = VVar Lvl
  | VHole Type
  deriving (Show, Eq, Ord)

-- | A single eliminator in a neutral's spine.
data Frame
  = VApp Type Value
  | VFst
  | VSnd
  | -- | A stuck case: the scrutinee is neutral.
    VCase Type Type Type Value Value
  | -- | A stuck absurd: the scrutinee is neutral at 'VoidTy'.
    VAbsurd Type
  | -- | A stuck if-then-else: the condition is neutral, so we can't choose a
    -- branch. Carries the motive type and both branch values.
    VIf Type Value Value
  deriving stock (Show, Eq, Ord)

pushFrame :: Neutral -> Frame -> Neutral
pushFrame Neutral {..} frame = Neutral {head = head, spine = Snoc spine frame}

-- | A closure pairs a function body with the environment it was defined in.
-- Instantiation extends the captured environment with the argument rather than
-- substituting. Closures also appear inside neutrals (as arguments in 'VApp'
-- frames).
data Closure = Closure {env :: SnocList Value, body :: Syntax}
  deriving stock (Show, Eq, Ord)

--------------------------------------------------------------------------------
-- Environment
--
-- The typechecker's context. Elaboration needs to track names (for resolving
-- named variables), types (for typechecking), and values (for quoting back from
-- the semantic domain). A 'Cell' bundles all three for each binding.

-- | A single binding in the context: a name, its type, and its value. The value
-- is a fresh neutral for lambda-bound variables (we don't know what they'll be
-- applied to) or an actual value for let-bound variables.
data Cell = Cell
  { cellName :: Name,
    cellType :: Type,
    cellValue :: Value
  }
  deriving stock (Show, Eq, Ord)

-- | The typechecker/elaboration context.
--
-- @locals@ is the evaluator's environment (values by de Bruijn index),
-- @localNames@ is for name resolution (searched linearly), and @size@ tracks
-- the current binding depth (used to generate fresh de Bruijn levels).
data Env = Env
  { locals :: SnocList Value,
    localNames :: [Cell],
    size :: Int,
    holes :: [Type]
  }
  deriving stock (Show, Eq, Ord)

initEnv :: Env
initEnv = Env Nil [] 0 mempty

extendLocalNames :: Env -> Cell -> Env
extendLocalNames e@Env {localNames} cell = e {localNames = cell : localNames}

extendHoles :: Type -> Env -> Env
extendHoles ty e@Env {holes} = e {holes = ty : holes}

bindCell :: Cell -> Env -> Env
bindCell cell@Cell {..} Env {..} =
  Env
    { locals = Snoc locals cellValue,
      localNames = cell : localNames,
      size = size + 1,
      holes = holes
    }

resolveCell :: Env -> Name -> Maybe Cell
resolveCell Env {..} bndr = find ((== bndr) . cellName) localNames

-- | Create a fresh neutral variable at the current depth. Used for lambda-bound
-- variables where we don't know the value.
freshVar :: Env -> Type -> Value
freshVar Env {size} ty = VNeutral ty $ Neutral (VVar $ Lvl size) Nil

-- | Create a fresh cell for a lambda-bound variable. The value is a neutral
-- because we don't know the argument yet.
freshCell :: Env -> Name -> Type -> Cell
freshCell ctx name ty = Cell name ty (freshVar ctx ty)

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
--
-- Each tactic returns the elaborated core IR: 'Check' returns @Type ->
-- TypecheckM Syntax@ and 'Synth' returns @TypecheckM (Type, Syntax)@. This is
-- the "elaboration." Typechecking and translation happen in one pass.

data Error
  = TypeError String
  | OutOfScopeError Name
  deriving (Show)

-- | Accumulated hole types from typechecking. Each time the typechecker
-- encounters a 'Hole' in check position, it 'tell's the expected type here.
newtype Holes = Holes {getHoles :: [Type]}
  deriving newtype (Show, Semigroup, Monoid)

newtype TypecheckM a = TypecheckM {runTypecheckM :: Env -> (Either Error a, Holes)}
  deriving
    (Functor, Applicative, Monad, MonadReader Env, MonadError Error, MonadWriter Holes)
    via (ExceptT Error (WriterT Holes (Reader Env)))

newtype Check = Check {runCheck :: Type -> TypecheckM Syntax}

newtype Synth = Synth {runSynth :: TypecheckM (Type, Syntax)}

synth :: Term -> Synth
synth = \case
  Var bndr -> varTactic bndr
  Ap tm1 tm2 -> lamElim (synth tm1) (check tm2)
  Anno ty tm -> annoTactic ty (check tm)
  Hole -> Synth $ throwError $ TypeError "Cannot sythesize holes"
  Fst tm -> pairElimFst (synth tm)
  Snd tm -> pairElimSnd (synth tm)
  tm -> Synth $ throwError $ TypeError $ "Cannot synthesize type for " <> show tm

check :: Term -> Check
check (Lam bndr body) = lamIntro bndr (check body)
check (Let bndr e body) = letTactic bndr (synth e) (check body)
check Hole = holeTactic
check (Pair tm1 tm2) = pairIntro (check tm1) (check tm2)
check (InL tm1) = sumIntroL (check tm1)
check (InR tm2) = sumIntroR (check tm2)
check (Case scrut (bndr1, t1) (bndr2, t2)) = sumElim (synth scrut) (check (Lam bndr1 t1)) (check (Lam bndr2 t2))
check (Absurd tm) = voidElim (synth tm)
check Unit = unitIntro
check Tru = boolIntroTrue
check Fls = boolIntroFalse
check (If tm1 tm2 tm3) = boolElim (check tm1) (check tm2) (check tm3)
check tm = subTactic (synth tm)

-- | Variable Resolution
--
-- Resolve a named variable to its type and elaborated form. This is where name
-- resolution happens.
--
-- we look up the name in 'localNames' to get the 'Cell', then quote the cell's
-- value back to 'Syntax' to produce the elaborated output.
--
-- The quoting step is what converts the de Bruijn level in the cell's value to
-- a de Bruijn index in the syntax.
--
-- (x : A) ∈ Γ
-- ─────────── Var⇒
--  Γ ⊢ x ⇒ A
varTactic :: Name -> Synth
varTactic bndr = Synth $ do
  ctx <- ask

  case resolveCell ctx bndr of
    Just Cell {..} -> do
      let quoted = flip runEvalM (locals ctx) $ quote (Lvl $ size ctx) cellType cellValue
      pure (cellType, quoted)
    Nothing -> throwError $ OutOfScopeError bndr

-- | Subsumption
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
subTactic subTac = Check $ \ty1 -> do
  (ty2, tm) <- runSynth subTac
  if ty2 == ty1
    then pure tm
    else throwError $ TypeError $ "Expected: " <> show ty1 <> ", but got: " <> show ty2

-- | Annotation
--
-- The annotation provides a type, switching from synth to check mode. We check
-- the body against the annotated type, then synthesize that type as the result.
-- The annotation itself is erased during elaboration, it doesn't appear in the
-- core 'Syntax'.
--
--    Γ ⊢ e ⇐ A
-- ─────────────── Anno⇒
-- Γ ⊢ (e : A) ⇒ A
annoTactic :: Type -> Check -> Synth
annoTactic ty annoTac = Synth $ do
  tm <- runCheck annoTac ty
  pure (ty, tm)

-- | Lambda Introduction
--
-- A lambda is checked against a function type. The expected type @A₁ → A₂@
-- tells us what type the parameter has (@A₁@), so we extend the context and
-- check the body against the return type (@A₂@). This is why lambdas can't
-- synthesize. Without the expected function type, we wouldn't know @A₁@.
--
-- Elaborates to @SLam name body'@.
--
--  Γ, x : A₁ ⊢ e ⇐ A₂
-- ──────────────────── LamIntro⇐
-- Γ ⊢ (λx.e) ⇐ A₁ → A₂
lamIntro :: Name -> Check -> Check
lamIntro bndr bodyTac = Check $ \case
  a `FuncTy` b -> do
    ctx <- ask
    let var = freshCell ctx bndr a
    fiber <- local (bindCell var) $ runCheck bodyTac b
    pure $ SLam bndr fiber
  _ -> throwError $ TypeError "Tried to introduce a lambda at a non-function type"

-- | Lambda Elimination
--
-- Application is a synth rule. Synthesize the function's type to get @A → B@,
-- then check the argument against @A@, and return @B@. The function type tells
-- us what to check the argument against. Information flows from the function to
-- the argument.
--
-- Elaborates to @SAp f' arg'@.
--
-- Γ ⊢ e₁ ⇒ A → B  Γ ⊢ e₂ ⇐ A
-- ────────────────────────── LamElim⇒
--       Γ ⊢ e₁ e₂ ⇒ B
lamElim :: Synth -> Check -> Synth
lamElim funcTac argTac =
  Synth $
    runSynth funcTac >>= \case
      (a `FuncTy` b, f) -> do
        arg <- runCheck argTac a
        pure (b, SAp f arg)
      (ty, _) -> throwError $ TypeError $ "Expected a function type but got " <> show ty

-- | Let Binding
--
-- @let x = e in body@ elaborates to @(λx. body') e'@. There is no dedicated
-- @SLet@ in the core syntax. The let is fully dissolved by NbE: the beta redex
-- reduces and the bound value is inlined into the normal form.
--
-- Unlike 'lamIntro', which binds a fresh neutral variable (since the argument
-- is unknown), the let tactic evaluates @e@ and stores the resulting value in
-- the context cell. This means references to @x@ in the body see the actual
-- value during elaboration, not a stuck variable.
--
--  Γ ⊢ e ⇒ A    Γ, x : A ⊢ body ⇐ B
--  ──────────────────────────────────── Let⇐
--        Γ ⊢ let x = e in body ⇐ B
letTactic :: Name -> Synth -> Check -> Check
letTactic bndr bndrTac bodyTac = Check $ \ty -> do
  (ty1, tm1) <- runSynth bndrTac
  ctx <- ask
  let val = runEvalM (eval tm1) (locals ctx)
      var = Cell bndr ty1 val
  fiber <- local (bindCell var) $ runCheck bodyTac ty
  pure $ SAp (SLam bndr fiber) tm1

-- | Type Hole
--
-- A hole accepts any expected type and records it via the 'Writer' effect.
-- Elaborates to @SHole ty@, which evaluates to a neutral and survives through
-- NbE.
--
-- The normal form still shows the hole with its type. Holes can only appear in
-- check position; in synth position there's no expected type to record, so it's
-- an error.
--
-- ────────── Hole⇐
--  Γ ⊢ ? ⇐ A
holeTactic :: Check
holeTactic = Check $ \ty -> do
  tell (Holes [ty])
  pure (SHole ty)

-- | Pair Introduction
--
-- Like lambdas, pairs are checked. the expected pair type @A × B@ tells us what
-- to check each component against.
--
-- Elaborates to @SPair a' b'@.
--
-- Γ ⊢ a ⇐ A   Γ ⊢ b ⇐ B
-- ───────────────────── Pair⇐
--  Γ ⊢ (a , b) ⇐ A × B
pairIntro :: Check -> Check -> Check
pairIntro checkFst checkSnd = Check $ \case
  PairTy a b -> do
    tm1 <- runCheck checkFst a
    tm2 <- runCheck checkSnd b
    pure (SPair tm1 tm2)
  ty -> throwError $ TypeError $ "Expected a Pair but got " <> show ty

-- | Pair Fst Elimination
--
-- Projection is a synth rule. Synthesize the pair's type to learn what the
-- components are, then return the appropriate one.
--
-- Γ ⊢ (t₁ , t₂) ⇒ A × B
-- ───────────────────── Fst⇒
--       Γ ⊢ t₁ ⇒ A
pairElimFst :: Synth -> Synth
pairElimFst fstTac =
  Synth $
    runSynth fstTac >>= \case
      (PairTy ty1 _ty2, tm) -> pure (ty1, SFst tm)
      (ty, _) -> throwError $ TypeError $ "Expected a Pair but got " <> show ty

-- | Pair Snd Elimination
--
-- Same as fst, but returns the second component.
--
-- Γ ⊢ (t₁ , t₂) ⇒ A × B
-- ───────────────────── Snd⇒
--       Γ ⊢ t₂ ⇒ B
pairElimSnd :: Synth -> Synth
pairElimSnd sndTac =
  Synth $
    runSynth sndTac >>= \case
      (PairTy _ty1 ty2, tm) -> pure (ty2, SSnd tm)
      (ty, _) -> throwError $ TypeError $ "Expected a Pair but got " <> show ty

-- | Sum Left Introduction
--
-- Checked against a sum type. The payload is checked against the left
-- component.
--
--      Γ ⊢ e ⇐ A
--  ───────────────── InL⇐
--  Γ ⊢ InL e ⇐ A + B
sumIntroL :: Check -> Check
sumIntroL inlTac = Check $ \case
  SumTy a _b -> SInL <$> runCheck inlTac a
  ty -> throwError $ TypeError $ "Expected a Sum type but got: " <> show ty

-- | Sum Right Introduction
--
-- Checked against a sum type. The payload is checked against the right
-- component.
--
--  Γ ⊢ e ⇐ B
--  ──────────────── InR⇐
--  Γ ⊢ InR e ⇐ A + B
sumIntroR :: Check -> Check
sumIntroR inrTac = Check $ \case
  SumTy _a b -> SInR <$> runCheck inrTac b
  ty -> throwError $ TypeError $ "Expected a Sum type but got: " <> show ty

-- | Sum Elimination
--
-- Synthesize the scrutinee's sum type, then check each branch as a
-- function from the injection's payload type to the motive. The
-- branches are elaborated as lambdas that bind the payload.
--
--  Γ ⊢ e ⇒ A + B    Γ ⊢ f ⇐ A → C    Γ ⊢ g ⇐ B → C
--  ─────────────────────────────────────────────── Case⇐
--                Γ ⊢ Case e f g ⇐ C
sumElim :: Synth -> Check -> Check -> Check
sumElim scrutTac checkT1 checkT2 = Check $ \ty -> do
  (scrutTy, scrut) <- runSynth scrutTac
  case scrutTy of
    SumTy a b -> do
      f <- runCheck checkT1 (FuncTy a ty)
      g <- runCheck checkT2 (FuncTy b ty)
      pure $ SCase scrut ty f g
    _ -> throwError $ TypeError $ "Expected a Sum type but got: " <> show scrutTy

-- | Void Elimination
--
-- Synthesize the scrutinee and verify it has type 'VoidTy'. Since no value of
-- type 'Void' exists, this branch is unreachable, but it can produce any type
-- @C@.
--
--  Γ ⊢ e ⇒ Void
--  ─────────────── Absurd⇐
--  Γ ⊢ absurd e ⇐ C
voidElim :: Synth -> Check
voidElim voidTac = Check $ \ty -> do
  (scrutTy, scrut) <- runSynth voidTac
  case scrutTy of
    VoidTy -> pure $ SAbsurd ty scrut
    _ -> throwError $ TypeError $ "Expected a Void but got: " <> show scrutTy

-- | Unit Introduction
--
-- Unit is a check rule, we verify the expected type is 'UnitTy'. There's
-- nothing to synthesize since @()@ doesn't carry type information.
--
-- Elaborates to 'SUnit'.
--
-- ───────────── Unit⇐
-- Γ ⊢ () ⇐ Unit
unitIntro :: Check
unitIntro = Check $ \case
  UnitTy -> pure SUnit
  ty -> throwError $ TypeError $ "Expected Unit type but got: " <> show ty

-- | Bool-True Introduction
--
-- Checked against 'BoolTy'. Elaborates to 'STru'.
--
-- ──────────────── True⇐
-- Γ ⊢ True ⇐ Bool
boolIntroTrue :: Check
boolIntroTrue = Check $ \case
  BoolTy -> pure STru
  ty -> throwError $ TypeError $ "Expected Bool type but got: " <> show ty

-- | Bool-False Introduction
--
-- Checked against 'BoolTy'. Elaborates to 'SFls'.
--
-- ──────────────── False⇐
-- Γ ⊢ False ⇐ Bool
boolIntroFalse :: Check
boolIntroFalse = Check $ \case
  BoolTy -> pure SFls
  ty -> throwError $ TypeError $ "Expected Bool type but got: " <> show ty

-- | Bool Elimination
--
-- Check the condition against 'BoolTy', and both branches against the expected
-- (motive) type. The motive is whatever type the @if@ expression is being
-- checked at. Elaborates to @SIf scrut' t' f'@.
--
-- Γ ⊢ t₁ ⇐ Bool  Γ ⊢ t₂ ⇐ T  Γ ⊢ t₃ ⇐ T
-- ───────────────────────────────────── If⇐
--   Γ ⊢ If t₁ then t₂ else t₃ ⇐ T
boolElim :: Check -> Check -> Check -> Check
boolElim checkT1 checkT2 checkT3 = Check $ \ty -> do
  tm1 <- runCheck checkT1 BoolTy
  tm2 <- runCheck checkT2 ty
  tm3 <- runCheck checkT3 ty
  pure (SIf tm1 ty tm2 tm3)

--------------------------------------------------------------------------------
-- Evaluator
--
-- The evaluator operates on 'Syntax' (the elaborated core IR) rather than
-- 'Term'. This is why elaboration matters, the evaluator doesn't need to deal
-- with named variables, annotations, or let bindings. It just sees de Bruijn
-- indices, lambdas, and applications.
--
-- Evaluation maps 'Syntax' to 'Value' under an environment. The interesting
-- cases are:
--
-- - 'SVar': look up the value in the environment by de Bruijn index.
-- - 'SLam': capture the current environment in a closure (don't evaluate the
--           body yet, since we don't know the argument).
-- - 'SAp': evaluate both sides, then apply. This is where beta reduction
--          happens, by instantiating the closure with the argument.

newtype EvalM a = EvalM {runEvalM :: SnocList Value -> a}
  deriving
    (Functor, Applicative, Monad, MonadReader (SnocList Value))
    via Reader (SnocList Value)

eval :: Syntax -> EvalM Value
eval = \case
  SVar (Ix ix) -> do
    env <- ask
    pure $ fromMaybe (error "internal error") $ nth env ix
  SLam bndr body -> do
    env <- ask
    pure $ VLam bndr (Closure env body)
  SAp tm1 tm2 -> do
    fun <- eval tm1
    arg <- eval tm2
    doApply fun arg
  SHole ty -> pure $ VNeutral ty (Neutral (VHole ty) Nil)
  SPair tm1 tm2 -> do
    tm1' <- eval tm1
    tm2' <- eval tm2
    pure $ VPair tm1' tm2'
  SFst tm -> eval tm >>= doFst
  SSnd tm -> eval tm >>= doSnd
  SInL tm -> VInL <$> eval tm
  SInR tm -> VInR <$> eval tm
  SCase t1 motive t2 t3 -> do
    t1' <- eval t1
    t2' <- eval t2
    t3' <- eval t3
    doCase t1' motive t2' t3'
  SAbsurd ty tm -> do
    tm' <- eval tm
    doAbsurd tm' ty
  SUnit -> pure VUnit
  STru -> pure VTru
  SFls -> pure VFls
  SIf p motive t1 t2 -> do
    p' <- eval p
    t1' <- eval t1
    t2' <- eval t2
    doIf p' motive t1' t2'

doApply :: Value -> Value -> EvalM Value
doApply (VLam _ clo) arg = appTermClosure clo arg
doApply (VNeutral (FuncTy ty1 ty2) neu) arg = pure $ VNeutral ty2 (pushFrame neu (VApp ty1 arg))
doApply _ _ = error "impossible case in doApply"

doFst :: Value -> EvalM Value
doFst (VPair a _b) = pure a
doFst (VNeutral (PairTy a _) neu) = pure $ VNeutral a (pushFrame neu VFst)
doFst _ = error "impossible case in doFst"

doSnd :: Value -> EvalM Value
doSnd (VPair _a b) = pure b
doSnd (VNeutral (PairTy _ b) neu) = pure $ VNeutral b (pushFrame neu VSnd)
doSnd _ = error "impossible case in doSnd"

doCase :: Value -> Type -> Value -> Value -> EvalM Value
doCase (VInL v) _motive f _ = doApply f v
doCase (VInR v) _motive _ g = doApply g v
doCase (VNeutral (SumTy a b) neu) motive f g =
  pure $ VNeutral motive (pushFrame neu (VCase (FuncTy a motive) (FuncTy b motive) motive f g))
doCase _ _ _ _ = error "impossible case in doCase"

doAbsurd :: Value -> Type -> EvalM Value
doAbsurd (VNeutral _ neu) ty = pure $ VNeutral ty (pushFrame neu (VAbsurd ty))
doAbsurd _ _ = error "impossible case in doAbsurd"

doIf :: Value -> Type -> Value -> Value -> EvalM Value
doIf VTru _ t1 _ = pure t1
doIf VFls _ _ t2 = pure t2
doIf (VNeutral _ neu) motive t1 t2 = pure $ VNeutral motive (pushFrame neu (VIf motive t1 t2))
doIf _ _ _ _ = error "impossible case in doIf"

appTermClosure :: Closure -> Value -> EvalM Value
appTermClosure (Closure env body) v = local (const $ Snoc env v) $ eval body

--------------------------------------------------------------------------------
-- Quoting
--
-- Quoting reads back a 'Value' into 'Syntax' (normal form). It is
-- type-directed, the type tells us how to handle each value.
--
-- At function types quoting eta-expands, so even a neutral gets wrapped in a
-- lambda. This ensures normal forms are fully eta-long, which means two terms
-- are beta-eta equal iff their normal forms are syntactically identical.
--
-- The 'Lvl' parameter tracks how many binders we've gone under, so we can
-- convert de Bruijn levels (stable under extension) back to de Bruijn indices
-- (what syntax uses).
--
-- Produces 'Syntax' rather than 'Term' since that's what the evaluator and
-- the output both use.
--
-- Holes quote back to @SHole@ via @quoteHead (VHole ty) = SHole ty@. Holes at
-- function types get eta-expanded during quoting (wrapped in a lambda), just
-- like neutral variables do.

-- | Quote a value to its beta-normal eta-long 'Syntax' form.
quote :: Lvl -> Type -> Value -> EvalM Syntax
quote l (FuncTy ty1 ty2) (VLam bndr clo@(Closure _env _body)) = do
  body <- bindVar ty1 l $ \v l' -> do
    clo <- appTermClosure clo v
    quote l' ty2 clo
  pure $ SLam bndr body
quote l (FuncTy ty1 ty2) f = do
  body <- bindVar ty1 l $ \v l' ->
    doApply f v >>= quote l' ty2
  pure $ SLam "_" body
quote l (PairTy ty1 ty2) (VPair tm1 tm2) = do
  tm1' <- quote l ty1 tm1
  tm2' <- quote l ty2 tm2
  pure $ SPair tm1' tm2'
quote l (SumTy a _b) (VInL tm) = SInL <$> quote l a tm
quote l (SumTy _a b) (VInR tm) = SInR <$> quote l b tm
quote _ _ VUnit = pure SUnit
quote _ _ VTru = pure STru
quote _ _ VFls = pure SFls
quote l _ (VNeutral _ neu) = quoteNeutral l neu
quote _ _ _ = error "impossible case in quote"

quoteLevel :: Lvl -> Lvl -> Ix
quoteLevel (Lvl l) (Lvl x) = Ix (l - (x + 1))

quoteNeutral :: Lvl -> Neutral -> EvalM Syntax
quoteNeutral l Neutral {..} = foldM (quoteFrame l) (quoteHead l head) spine

quoteHead :: Lvl -> Head -> Syntax
quoteHead l (VVar lvl) = SVar (quoteLevel l lvl)
quoteHead _ (VHole ty) = SHole ty

quoteFrame :: Lvl -> Syntax -> Frame -> EvalM Syntax
quoteFrame l tm = \case
  VApp ty arg -> SAp tm <$> quote l ty arg
  VFst -> pure $ SFst tm
  VSnd -> pure $ SSnd tm
  VCase tyF tyG mot f g -> do
    f' <- quote l tyF f
    g' <- quote l tyG g
    pure $ SCase tm mot f' g'
  VAbsurd ty -> pure $ SAbsurd ty tm
  VIf ty t1 t2 -> liftA2 (SIf tm ty) (quote l ty t1) (quote l ty t2)

bindVar :: Type -> Lvl -> (Value -> Lvl -> a) -> a
bindVar ty lvl f =
  let v = VNeutral ty $ Neutral (VVar lvl) Nil
   in f v $ incLevel lvl

--------------------------------------------------------------------------------
-- Main

run :: Term -> Either (Error, Holes) (RunResult Syntax Type Syntax, Holes)
run term =
  case runTypecheckM (runSynth $ synth term) initEnv of
    (Left err, holes) -> Left (err, holes)
    (Right (type', syntax), holes) -> do
      let result = flip runEvalM Nil $ do
            value <- eval syntax
            quote initLevel type' value
      pure (RunResult syntax type' result, holes)

main :: IO ()
main = do
  let test = runTest run
      testErr = runTestErr run

  putStrLn "=== Typed Holes ==="
  putStrLn ""

  -- Hole in checked position — takes on the expected type
  section "Hole in Checked Position"
  test
    "? checked at Unit — hole takes type Unit"
    (Anno UnitTy Hole)
  test
    "? checked at Unit -> Unit — hole takes function type"
    (Anno (UnitTy `FuncTy` UnitTy) Hole)
  test
    "? checked at (Unit * Unit) — hole takes pair type"
    (Anno (PairTy UnitTy UnitTy) Hole)
  putStrLn ""

  -- Hole in lambda body — infers type from context
  section "Hole in Lambda Body"
  test
    "\\x. ? : Unit -> Unit — hole gets type Unit"
    ( Anno
        (UnitTy `FuncTy` UnitTy)
        (Lam "x" Hole)
    )
  test
    "\\x. ? : Unit -> (Unit * Unit) — hole gets pair type"
    ( Anno
        (UnitTy `FuncTy` PairTy UnitTy UnitTy)
        (Lam "x" Hole)
    )
  test
    "\\f. \\x. ? : (Unit -> Unit) -> Unit -> Unit — hole gets Unit"
    ( Anno
        ((UnitTy `FuncTy` UnitTy) `FuncTy` (UnitTy `FuncTy` UnitTy))
        (Lam "f" (Lam "x" Hole))
    )
  putStrLn ""

  -- Hole in pair components
  section "Hole in Pair"
  test
    "(?, ()) : Unit * Unit — hole in fst"
    ( Anno
        (PairTy UnitTy UnitTy)
        (Pair Hole Unit)
    )
  test
    "((), ?) : Unit * Unit — hole in snd"
    ( Anno
        (PairTy UnitTy UnitTy)
        (Pair Unit Hole)
    )
  test
    "(?, ?) : Unit * Unit — holes in both"
    ( Anno
        (PairTy UnitTy UnitTy)
        (Pair Hole Hole)
    )
  putStrLn ""

  -- Holes at complex types
  section "Holes at Complex Types"
  test
    "\\f. ? : (Unit -> Unit) -> Unit — hole at Unit in higher-order context"
    ( Anno
        ((UnitTy `FuncTy` UnitTy) `FuncTy` UnitTy)
        (Lam "f" Hole)
    )
  test
    "\\f. (f ?, ?) : (Unit -> Unit) -> Unit * Unit — holes at different positions"
    ( Anno
        ((UnitTy `FuncTy` UnitTy) `FuncTy` PairTy UnitTy UnitTy)
        (Lam "f" (Pair (Ap (Var "f") Hole) Hole))
    )
  test
    "(?, ((), ?)) : Unit * (Unit * Unit) — holes in nested pair"
    ( Anno
        (PairTy UnitTy (PairTy UnitTy UnitTy))
        (Pair Hole (Pair Unit Hole))
    )
  test
    "\\x. \\y. ? : Unit -> (Unit -> Unit) -> Unit * Unit — hole gets pair type under two binders"
    ( Anno
        (UnitTy `FuncTy` ((UnitTy `FuncTy` UnitTy) `FuncTy` PairTy UnitTy UnitTy))
        (Lam "x" (Lam "y" Hole))
    )
  putStrLn ""

  -- Hole as function argument — goes through sub tactic
  section "Hole as Function Argument"
  test
    "(\\x. x : Unit -> Unit) ? — hole elaborated as argument"
    ( Ap
        (Anno (UnitTy `FuncTy` UnitTy) (Lam "x" (Var "x")))
        (Anno UnitTy Hole)
    )
  test
    "(\\f. f : (Unit -> Unit) -> (Unit -> Unit)) ? — hole at function type as argument"
    ( Ap
        ( Anno
            ((UnitTy `FuncTy` UnitTy) `FuncTy` (UnitTy `FuncTy` UnitTy))
            (Lam "f" (Var "f"))
        )
        (Anno (UnitTy `FuncTy` UnitTy) Hole)
    )
  putStrLn ""

  -- Holes flow through the bool/sum check positions: an if branch, a sum
  -- payload, and a case branch body each push their expected type into the
  -- hole.
  section "Holes in Bool / Sum Positions"
  test
    "if True then ? else False : the then-branch hole records Bool"
    (Anno BoolTy (If Tru Hole Fls))
  test
    "inl ? : Bool + Unit : the payload hole records Bool"
    (Anno (SumTy BoolTy UnitTy) (InL Hole))
  test
    "case (inl True) of inl x -> ? | inr y -> False : the branch hole records Bool"
    ( Anno
        BoolTy
        (Case (Anno (SumTy BoolTy UnitTy) (InL Tru)) ("x", Hole) ("y", Fls))
    )
  putStrLn ""

  -- Hole in synthesized position — cannot synthesize
  section "Hole in Synth Position (expected failure)"
  testErr
    "bare ? — cannot synthesize hole"
    Hole
  testErr
    "? applied to () — cannot synthesize function hole"
    (Ap Hole Unit)
  testErr
    "absurd ? — the scrutinee is synthesized, so the hole cannot appear there"
    (Anno BoolTy (Absurd Hole))

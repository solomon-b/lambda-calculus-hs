{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- | System T, natural numbers and primitive recursion.
--
-- Extends the type system with natural numbers ('NatTy') and booleans
-- ('BoolTy'). Natural numbers are introduced by 'Zero' and 'Succ', and
-- eliminated by 'NatRec' (Gödel's primitive recursor), which takes a base case,
-- a step function of type @Nat -> T -> T@ (receiving the predecessor and the
-- recursive result), and a scrutinee. This gives us a total language where
-- every well-typed program terminates.
module Main where

--------------------------------------------------------------------------------

import Control.Monad (foldM, (>=>))
import Control.Monad.Except (MonadError (..))
import Control.Monad.Identity
import Control.Monad.Reader (MonadReader (..))
import Control.Monad.State.Strict (MonadState (..), gets, modify)
import Control.Monad.Trans.Except (ExceptT (..))
import Control.Monad.Trans.Reader (Reader, ReaderT (..))
import Control.Monad.Trans.State.Strict (StateT (..))
import Control.Monad.Trans.Writer.Strict (WriterT (..))
import Control.Monad.Writer.Strict (MonadWriter (..))
import Data.Foldable (find)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
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
-- New in this module: booleans ('Tru', 'Fls', 'If') and natural numbers
-- ('Zero', 'Succ', 'NatRec') in both the surface syntax and core IR.

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
    SumCase Term (Name, Term) (Name, Term)
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
  | -- | Zero, the base case for natural numbers.
    Zero
  | -- | Successor of a natural number.
    Succ Term
  | -- | Primitive recursion: @NatRec base step scrut@ eliminates a natural
    -- number. At zero it returns @base@; at @Succ n@ it applies @step@ to the
    -- predecessor @n@ and the recursive result.
    NatRec Term Term Term
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
prettyTerm p (InL e) =
  parensIf (p > appPrec) $
    "inl" PP.<+> prettyTerm atomPrec e
prettyTerm p (InR e) =
  parensIf (p > appPrec) $
    "inr" PP.<+> prettyTerm atomPrec e
prettyTerm p (SumCase scrut (ln, l) (rn, r)) =
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
prettyTerm p (Absurd e) =
  parensIf (p > appPrec) $
    "absurd" PP.<+> prettyTerm atomPrec e
prettyTerm _ Unit = "()"
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
prettyTerm _ Zero = "0"
prettyTerm p (Succ e) =
  parensIf (p > appPrec) $
    "S" PP.<+> prettyTerm atomPrec e
prettyTerm p (NatRec base step scrut) =
  parensIf (p > appPrec) $
    "natrec" PP.<+> prettyTerm atomPrec base PP.<+> prettyTerm atomPrec step PP.<+> prettyTerm atomPrec scrut

instance PP.Pretty Term where
  pretty = prettyTerm lamPrec

-- | A metavariable identifier. A metavariable is an unknown type; it
-- rides through 'Syntax' and 'Value' as an opaque atomic head, since a
-- hole evaluates to a neutral and quoting a neutral ignores its type. It
-- is resolved only in the typechecker, never by the evaluator.
newtype MetaId = MetaId Int
  deriving (Eq, Ord, Show)

-- | The type language. Functions, pairs, unit, booleans, and natural numbers.
data Type
  = -- | Function type. @A -> B@.
    FuncTy Type Type
  | -- | Pair type. @A * B@.
    PairTy Type Type
  | -- | Binary sum: @A + B@.
    SumTy Type Type
  | -- | Bool Type. @Bool@.
    BoolTy
  | -- | Unit type. @Unit@.
    UnitTy
  | -- | The empty type. No values inhabit it.
    VoidTy
  | -- | Natural Numbers Type. @Nat@.
    NatTy
  | -- | A metavariable: an unknown type, to be solved by unification.
    MetaTy MetaId
  deriving stock (Show, Eq, Ord)

prettyType :: Prec -> Type -> PP.Doc ann
prettyType p (FuncTy a b) =
  parensIf (p > arrowPrec) $
    prettyType (arrowPrec + 1) a PP.<+> arrowSym PP.<+> prettyType arrowPrec b
prettyType p (PairTy a b) =
  parensIf (p > arrowPrec) $
    prettyType (arrowPrec + 1) a PP.<+> "*" PP.<+> prettyType arrowPrec b
prettyType p (SumTy a b) =
  parensIf (p > PP.sumPrec) $
    prettyType (PP.sumPrec + 1) a PP.<+> "+" PP.<+> prettyType PP.sumPrec b
prettyType _ UnitTy = "Unit"
prettyType _ VoidTy = "Void"
prettyType _ BoolTy = "Bool"
prettyType _ NatTy = "Nat"
prettyType _ (MetaTy (MetaId n)) = "?" <> PP.pretty n

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
  | -- | Lambda abstraction.
    SLam Name Syntax
  | -- | Function application.
    SAp Syntax Syntax
  | -- | A hole carrying the expected type. Evaluates to a
    -- neutral so it propagates through NbE.
    SHole Type
  | -- | Pair introduction.
    SPair Syntax Syntax
  | -- | First projection of a pair.
    SFst Syntax
  | -- | Second projection of a pair.
    SSnd Syntax
  | -- | Left injection into a sum type. @inl x@.
    SInL Syntax
  | -- | Right injection into a sum type. @inr x@.
    SInR Syntax
  | -- | Case analysis on a sum type. @case scrut of inl x -> l; inr y -> r@.
    SSumCase Syntax Type Syntax Syntax
  | -- | Elimination of the empty type. @absurd t@.
    SAbsurd Type Syntax
  | -- | The unit value.
    SUnit
  | -- | Boolean true.
    STru
  | -- | Boolean false.
    SFls
  | -- | Conditional. @if scrut then t else f@.
    SIf Syntax Type Syntax Syntax
  | -- | Zero, the base case for natural numbers.
    SZero
  | -- | Successor of a natural number.
    SSucc Syntax
  | -- | Primitive recursion on natural numbers. @NatRec base step scrut@
    -- eliminates a natural number. At zero it returns @base@; at @Succ n@
    -- it applies @step@ to the predecessor @n@ and the recursive result.
    SNatRec Type Syntax Syntax Syntax
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
  | -- | Boolean true.
    VTru
  | -- | Boolean false.
    VFls
  | -- | The unit value.
    VUnit
  | -- | The natural number zero.
    VZero
  | -- | Successor of a natural number value.
    VSucc Value
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
    VSumCase Type Type Type Value Value
  | -- | A stuck absurd: the scrutinee is neutral at 'VoidTy'.
    VAbsurd Type
  | -- | A stuck if-then-else: the condition is neutral, so we can't choose a
    -- branch. Carries the motive type and both branch values.
    VIf Type Value Value
  | -- | A stuck primitive recursion: the scrutinee is neutral. Carries the
    -- motive type, the base case value, and the step function value.
    VNatRec Type Value Value
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
data TypeCheckEnv = TypeCheckEnv
  { locals :: SnocList Value,
    localNames :: [Cell],
    size :: Int,
    -- | Holes encountered during typechecking
    holes :: [Type]
  }
  deriving stock (Show, Eq, Ord)

-- | The evaluator's environment. Carries two independent snoc lists: one for
-- term variable bindings ('Value') and one for type variable bindings
-- ('VType'). The lengths track the current depth in each index space. Used both
-- as the top-level eval environment and captured inside closures.
newtype EvalEnv = EvalEnv
  { -- | Term variable bindings, indexed by de Bruijn index.
    envValues :: SnocList Value
  }
  deriving stock (Show, Eq, Ord)

-- | Project the evaluator environment from the typechecker context. The
-- typechecker carries extra metadata (names, holes, ADT specs) that the
-- evaluator does not need.
toEvalEnv :: TypeCheckEnv -> EvalEnv
toEvalEnv env = EvalEnv {envValues = env.locals}

initEnv :: TypeCheckEnv
initEnv = TypeCheckEnv Nil [] 0 mempty

extendLocalNames :: TypeCheckEnv -> Cell -> TypeCheckEnv
extendLocalNames e@TypeCheckEnv {localNames} cell = e {localNames = cell : localNames}

extendHoles :: Type -> TypeCheckEnv -> TypeCheckEnv
extendHoles ty e@TypeCheckEnv {holes} = e {holes = ty : holes}

bindCell :: Cell -> TypeCheckEnv -> TypeCheckEnv
bindCell cell@Cell {..} TypeCheckEnv {..} =
  TypeCheckEnv
    { locals = Snoc locals cellValue,
      localNames = cell : localNames,
      size = size + 1,
      holes = holes
    }

resolveCell :: TypeCheckEnv -> Name -> Maybe Cell
resolveCell TypeCheckEnv {..} bndr = find ((== bndr) . cellName) localNames

-- | Create a fresh neutral variable at the current depth. Used for lambda-bound
-- variables where we don't know the value.
freshVar :: TypeCheckEnv -> Type -> Value
freshVar TypeCheckEnv {size} ty = VNeutral ty $ Neutral (VVar $ Lvl size) Nil

-- | Create a fresh cell for a lambda-bound variable. The value is a neutral
-- because we don't know the argument yet.
freshCell :: TypeCheckEnv -> Name -> Type -> Cell
freshCell ctx name ty = Cell name ty (freshVar ctx ty)

--------------------------------------------------------------------------------
-- Unification
--
-- A metavariable is an unknown type, written 'MetaTy' and carried as an
-- atomic head alongside the other type formers. The evaluator never
-- inspects one, so the whole solving apparatus lives here in the
-- typechecker, in the 'TypecheckM' state.
--
-- The state is the 'MetaCtx': a counter for minting fresh metavariables
-- and a map from each to its solution. 'freshMeta' mints a new unknown,
-- 'force' resolves a head far enough to see whether it is rigid or still
-- a metavariable, 'solveMeta' records a solution after an occurs check,
-- and 'unify' makes two types equal by solving metavariables.
--
-- 'zonk' and 'zonkSyntax' replace every solved metavariable with its
-- solution. They run before anything crosses into the evaluator, which
-- has no access to the solution map.

-- | The unification state: a counter for minting fresh metavariables and
-- a map from each metavariable to its solution.
data MetaCtx = MetaCtx {next :: MetaId, solutions :: Map MetaId Type}

-- | The empty unification state: no metavariables minted, none solved.
initMetas :: MetaCtx
initMetas = MetaCtx (MetaId 0) mempty

-- | The successor metavariable id.
nextMetaId :: MetaId -> MetaId
nextMetaId (MetaId n) = MetaId (n + 1)

-- | Mint a fresh, unsolved metavariable. Bumps the counter and returns
-- the new 'MetaTy'.
freshMeta :: TypecheckM Type
freshMeta = do
  i <- gets next
  modify (\m -> m {next = nextMetaId m.next})
  pure $ MetaTy i

-- | Record the solution @meta := ty@, guarded by an occurs check.
--
-- The check forces at every node as it descends, so it catches @meta@
-- hiding behind an already solved metavariable. If @meta@ occurs in @ty@
-- the solution would be infinite (e.g. @?a := ?a -> ?a@), so we reject it
-- with 'InfiniteTypeError'. Otherwise we store the forced @ty@, keeping
-- the map free of stale metavariable heads.
solveMeta :: MetaId -> Type -> TypecheckM ()
solveMeta meta ty = do
  occured <- occurs ty
  if occured
    then throwError $ InfiniteTypeError ty
    else do
      ty' <- force ty
      modify $ \ctx -> ctx {solutions = Map.insert meta ty' ctx.solutions}
  where
    occurs =
      force >=> \case
        MetaTy m -> pure (m == meta)
        FuncTy a b -> (||) <$> occurs a <*> occurs b
        PairTy a b -> (||) <$> occurs a <*> occurs b
        SumTy a b -> (||) <$> occurs a <*> occurs b
        _ -> pure False

-- | Resolve a type's head. A solved metavariable is chased to its
-- solution (and on, until the head is rigid or unsolved); anything else
-- is returned unchanged. This is shallow: it resolves only the head, not
-- the interior, which is all a consumer needs to tell whether the head is
-- rigid or flexible. Termination relies on the solution map being
-- acyclic, which the occurs check in 'solveMeta' guarantees.
force :: Type -> TypecheckM Type
force = \case
  MetaTy m ->
    gets (Map.lookup m . solutions) >>= \case
      Just ty -> force ty
      Nothing -> pure (MetaTy m)
  ty -> pure ty

-- | Resolve every metavariable in a type, head and interior alike. The
-- deep counterpart of 'force', used for display and before a type crosses
-- into the evaluator. A metavariable that survives a zonk is genuinely
-- unsolved and is shown as @?n@.
zonk :: Type -> TypecheckM Type
zonk =
  force >=> \case
    FuncTy a b -> FuncTy <$> zonk a <*> zonk b
    PairTy a b -> PairTy <$> zonk a <*> zonk b
    SumTy a b -> SumTy <$> zonk a <*> zonk b
    ty -> pure ty

-- | Resolve every metavariable embedded in an elaborated term. The core
-- 'Syntax' carries types: the type of each hole and the motive of each
-- eliminator. The evaluator cannot resolve a metavariable, so the term is
-- zonked before evaluation. The traversal recurses through the whole
-- tree, zonking each embedded type and leaving the term structure intact.
zonkSyntax :: Syntax -> TypecheckM Syntax
zonkSyntax = \case
  SLam nm bdy -> SLam nm <$> zonkSyntax bdy
  SAp f a -> SAp <$> zonkSyntax f <*> zonkSyntax a
  SHole ty -> SHole <$> zonk ty
  SPair a b -> SPair <$> zonkSyntax a <*> zonkSyntax b
  SFst tm -> SFst <$> zonkSyntax tm
  SSnd tm -> SSnd <$> zonkSyntax tm
  SIf s ty t f -> SIf <$> zonkSyntax s <*> zonk ty <*> zonkSyntax t <*> zonkSyntax f
  SAbsurd ty tm -> SAbsurd <$> zonk ty <*> zonkSyntax tm
  SInL tm -> SInL <$> zonkSyntax tm
  SInR tm -> SInR <$> zonkSyntax tm
  SSumCase scrut ty f g -> SSumCase <$> zonkSyntax scrut <*> zonk ty <*> zonkSyntax f <*> zonkSyntax g
  SSucc tm -> SSucc <$> zonkSyntax tm
  SNatRec ty base step scrut -> SNatRec <$> zonk ty <*> zonkSyntax base <*> zonkSyntax step <*> zonkSyntax scrut
  syn -> pure syn

-- | Make two types equal by solving metavariables.
--
-- Both heads are forced first. Two identical metavariables are already
-- equal. A flexible head (an unsolved metavariable) is solved to the
-- other side. Two rigid heads of the same former are decomposed and
-- unified componentwise. Anything else is a rigid mismatch. This is first
-- order and syntactic, so it is complete: if a unifier exists, it is
-- found.
unify :: Type -> Type -> TypecheckM ()
unify a b = do
  a' <- force a
  b' <- force b
  case (a', b') of
    (MetaTy m, MetaTy n)
      | m == n -> pure ()
      | otherwise -> solveMeta m b'
    (MetaTy m, _) -> solveMeta m b'
    (_, MetaTy n) -> solveMeta n a'
    (FuncTy x1 y1, FuncTy x2 y2) -> unify x1 x2 >> unify y1 y2
    (SumTy x1 y1, SumTy x2 y2) -> unify x1 x2 >> unify y1 y2
    (PairTy x1 y1, PairTy x2 y2) -> unify x1 x2 >> unify y1 y2
    _
      | a' == b' -> pure ()
      | otherwise -> throwError (UnificationError a' b')

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
-- synthesized. The 'switchTactic' bridges the two directions.
--
-- Each tactic returns the elaborated core IR: 'Check' returns @Type ->
-- TypecheckM Syntax@ and 'Synth' returns @TypecheckM (Type, Syntax)@. This is
-- the "elaboration." Typechecking and translation happen in one pass.

data Error
  = TypeError String
  | UnknownVariable Name
  | InfiniteTypeError Type
  | UnificationError Type Type
  | OutOfScopeError Name
  deriving (Show)

-- | Accumulated hole types from typechecking. Each time the typechecker
-- encounters a 'Hole' in check position, it 'tell's the expected type here.
newtype Holes = Holes {getHoles :: [Type]}
  deriving newtype (Show, Semigroup, Monoid)

newtype TypecheckM a = TypecheckM {runTypecheckM :: MetaCtx -> TypeCheckEnv -> ((Either Error a, Holes), MetaCtx)}
  deriving
    (Functor, Applicative, Monad, MonadState MetaCtx, MonadReader TypeCheckEnv, MonadError Error, MonadWriter Holes)
    via (ExceptT Error (WriterT Holes (StateT MetaCtx (Reader TypeCheckEnv))))

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
check Tru = boolIntroTrue
check Fls = boolIntroFalse
check (If tm1 tm2 tm3) = boolElim (check tm1) (check tm2) (check tm3)
check Unit = unitIntro
check Zero = natIntroZero
check (Succ tm) = natIntroSucc (check tm)
check (NatRec tm1 tm2 n) = natElim (check tm1) (check tm2) (check n)
check tm = switchTactic (synth tm)

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
-- The cell's type is zonked first. Quoting is type directed and runs in the
-- evaluator, which cannot resolve a metavariable, so a binder whose type is a
-- solved metavariable would otherwise crash the quote.
--
-- (x : A) ∈ Γ
-- ─────────── Var⇒
--  Γ ⊢ x ⇒ A
varTactic :: Name -> Synth
varTactic bndr = Synth $ do
  ctx <- ask

  case resolveCell ctx bndr of
    Just Cell {..} -> do
      ty <- zonk cellType
      let quoted = flip runEvalM (toEvalEnv ctx) $ quote (Lvl $ size ctx) ty cellValue
      pure (ty, quoted)
    Nothing -> throwError $ UnknownVariable bndr

-- | Switch
--
-- The bridge between synth and check. Synthesize a type for the term, then
-- unify it with the expected type, solving metavariables on either side. This
-- is how a synthesizable term (like a variable or annotation) can appear in a
-- checked position. Every term that doesn't have its own check rule falls
-- through to this. It is the canonical place unification fires: a synthesized
-- type meeting an expected one.
--
-- Γ ⊢ e ⇒ A  A ≡ B
-- ──────────────── Switch⇐
--    Γ ⊢ e ⇐ B
switchTactic :: Synth -> Check
switchTactic switchTac = Check $ \ty1 -> do
  (ty2, tm) <- runSynth switchTac
  unify ty2 ty1

  pure tm

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
annoTactic ty bndrTac = Synth $ do
  tm <- runCheck bndrTac ty
  pure (ty, tm)

-- | Lambda Introduction
--
-- A lambda is checked against a function type. The expected type @A₁ → A₂@
-- tells us what type the parameter has (@A₁@), so we extend the context and
-- check the body against the return type (@A₂@). This is why lambdas can't
-- synthesize. Without the expected function type, we wouldn't know @A₁@.
--
-- The expected type is unified with a fresh @?a -> ?b@ rather than matched
-- directly: if it is already a function type this recovers the domain and
-- codomain, and if it is a flexible metavariable, unification solves it to
-- that function shape (imitation).
--
-- Elaborates to @SLam name body'@.
--
--  Γ, x : A₁ ⊢ e ⇐ A₂
-- ──────────────────── LamIntro⇐
-- Γ ⊢ (λx.e) ⇐ A₁ → A₂
lamIntro :: Name -> Check -> Check
lamIntro bndr bodyTac = Check $ \ty -> do
  a <- freshMeta
  b <- freshMeta
  unify ty (FuncTy a b)
  a' <- force a

  ctx <- ask
  let var = freshCell ctx bndr a'
  fiber <- local (bindCell var) $ runCheck bodyTac b
  pure $ SLam bndr fiber

-- | Lambda Elimination
--
-- Application is a synth rule. Synthesize the function's type, unify it with a
-- fresh @?a -> ?b@, check the argument against @?a@, and return @?b@. The
-- unification recovers the domain and codomain when the function type is
-- known, and solves a flexible head into a function shape when it is a
-- metavariable (imitation). Information flows from the function to the
-- argument.
--
-- Elaborates to @SAp f' arg'@.
--
-- Γ ⊢ e₁ ⇒ A → B  Γ ⊢ e₂ ⇐ A
-- ────────────────────────── LamElim⇒
--       Γ ⊢ e₁ e₂ ⇒ B
lamElim :: Synth -> Check -> Synth
lamElim funcTac argTac = Synth $ do
  (ty, f) <- runSynth funcTac
  a <- freshMeta
  b <- freshMeta
  unify ty (FuncTy a b)

  arg <- runCheck argTac a
  pure (b, SAp f arg)

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
  let val = runEvalM (eval tm1) (toEvalEnv ctx)
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

holeSynthTactic :: Synth
holeSynthTactic = Synth $ do
  m <- freshMeta
  tell (Holes [m])
  pure (m, SHole m)

-- | Pair Introduction
--
-- Like lambdas, pairs are checked. The expected type is unified with a fresh
-- @?a * ?b@: when it is a known pair type this recovers the component types to
-- check against, and when it is a flexible metavariable, unification solves it
-- to a pair shape (imitation).
--
-- Elaborates to @SPair a' b'@.
--
-- Γ ⊢ a ⇐ A   Γ ⊢ b ⇐ B
-- ───────────────────── Pair⇐
--  Γ ⊢ (a , b) ⇐ A × B
pairIntro :: Check -> Check -> Check
pairIntro checkFst checkSnd = Check $ \ty -> do
  a <- freshMeta
  b <- freshMeta
  unify ty (PairTy a b)

  tm1 <- runCheck checkFst a
  tm2 <- runCheck checkSnd b
  pure (SPair tm1 tm2)

-- | Pair Fst Elimination
--
-- Projection is a synth rule. Synthesize the operand's type and unify it with
-- a fresh @?a * ?b@, then return the first component. When the operand is a
-- hole, the unification solves its metavariable to a pair (imitation), so
-- @fst _@ learns the hole is a pair and reports the skeleton.
--
-- Γ ⊢ (t₁ , t₂) ⇒ A × B
-- ───────────────────── Fst⇒
--       Γ ⊢ t₁ ⇒ A
pairElimFst :: Synth -> Synth
pairElimFst fstTac = Synth $ do
  (ty, tm) <- runSynth fstTac
  a <- freshMeta
  b <- freshMeta
  unify ty (PairTy a b)

  pure (a, SFst tm)

-- | Pair Snd Elimination
--
-- Same as fst, but returns the second component.
--
-- Γ ⊢ (t₁ , t₂) ⇒ A × B
-- ───────────────────── Snd⇒
--       Γ ⊢ t₂ ⇒ B
pairElimSnd :: Synth -> Synth
pairElimSnd sndTac = Synth $ do
  (ty, tm) <- runSynth sndTac
  a <- freshMeta
  b <- freshMeta
  unify ty (PairTy a b)

  pure (b, SSnd tm)

-- | Bool-True Introduction
--
-- Checked against 'BoolTy'.
--
-- ──────────────── True⇐
-- Γ ⊢ True ⇐ Bool
boolIntroTrue :: Check
boolIntroTrue = Check $ \ty -> unify ty BoolTy >> pure STru

-- | Bool-False Introduction
--
-- Checked against 'BoolTy'. Elaborates to 'SFls'.
--
-- ──────────────── False⇐
-- Γ ⊢ False ⇐ Bool
boolIntroFalse :: Check
boolIntroFalse = Check $ \ty -> unify ty BoolTy >> pure SFls

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
boolElim pTac tTac fTac = Check $ \ty -> do
  tm1 <- runCheck pTac BoolTy
  tm2 <- runCheck tTac ty
  tm3 <- runCheck fTac ty
  pure (SIf tm1 ty tm2 tm3)

-- | Unit Introduction
--
-- Unify the expected type with 'UnitTy'. When the expected type is a
-- flexible metavariable, this solves it to 'UnitTy'.
--
-- ───────────── Unit⇐
-- Γ ⊢ () ⇐ Unit
unitIntro :: Check
unitIntro = Check $ \ty -> unify ty UnitTy >> pure SUnit

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
  unify scrutTy VoidTy

  pure $ SAbsurd ty scrut

-- | Sum Left Introduction
--
-- Checked against a sum type. The expected type is unified with a fresh
-- @?a + ?b@ and the payload is checked against the left component @?a@.
-- Building a left injection says nothing about the right summand, so @?b@
-- is left unsolved.
--
--      Γ ⊢ e ⇐ A
--  ───────────────── InL⇐
--  Γ ⊢ InL e ⇐ A + B
sumIntroL :: Check -> Check
sumIntroL inlTac = Check $ \ty -> do
  a <- freshMeta
  b <- freshMeta
  unify ty (SumTy a b)

  tm <- runCheck inlTac a
  pure (SInL tm)

-- | Sum Right Introduction
--
-- Checked against a sum type. The expected type is unified with a fresh
-- @?a + ?b@ and the payload is checked against the right component @?b@.
-- Building a right injection says nothing about the left summand, so @?a@
-- is left unsolved.
--
--  Γ ⊢ e ⇐ B
--  ──────────────── InR⇐
--  Γ ⊢ InR e ⇐ A + B
sumIntroR :: Check -> Check
sumIntroR inrTac = Check $ \ty -> do
  a <- freshMeta
  b <- freshMeta
  unify ty (SumTy a b)

  tm <- runCheck inrTac b
  pure (SInR tm)

-- | Sum Elimination
--
-- Synthesize the scrutinee's type and unify it with a fresh @?a + ?b@,
-- then check each branch as a function from its payload type to the
-- motive. The branches are elaborated as lambdas that bind the payload.
-- When the scrutinee is a hole, the unification solves its metavariable
-- to a sum (imitation), so @case _ of …@ learns the hole is a sum.
--
--  Γ ⊢ e ⇒ A + B    Γ ⊢ f ⇐ A → C    Γ ⊢ g ⇐ B → C
--  ─────────────────────────────────────────────── SumCase⇐
--                Γ ⊢ SumCase e f g ⇐ C
sumElim :: Synth -> Check -> Check -> Check
sumElim scrutTac leftTac rightTac = Check $ \ty -> do
  (scrutTy, scrut) <- runSynth scrutTac
  a <- freshMeta
  b <- freshMeta
  unify scrutTy (SumTy a b)

  f <- runCheck leftTac (FuncTy a ty)
  g <- runCheck rightTac (FuncTy b ty)
  pure $ SSumCase scrut ty f g

-- | Nat Zero Introduction
--
-- Checked against 'NatTy'. Elaborates to 'SZero'.
--
-- ───────── Zero⇐
-- Γ ⊢ 0 ⇐ ℕ
natIntroZero :: Check
natIntroZero = Check $ \ty -> unify ty NatTy >> pure SZero

-- | Nat Succ Introduction
--
-- Checked against 'NatTy'. The argument is also checked against 'NatTy'.
-- Elaborates to @SSucc t'@.
--
--   Γ ⊢ t ⇐ ℕ
-- ────────────── Succ⇐
-- Γ ⊢ Succ t ⇐ ℕ
natIntroSucc :: Check -> Check
natIntroSucc baseTac = Check $ \ty -> do
  unify ty NatTy
  SSucc <$> runCheck baseTac NatTy

-- | Nat Elimination (Gödel's primitive recursor)
--
-- The scrutinee is checked at 'NatTy'. The base case is checked at the motive
-- type @T@. The step function is checked at @ℕ → T → T@: it receives the
-- predecessor and the recursive result, and returns a @T@. This is what makes
-- it primitive recursion rather than simple iteration, the step function has
-- access to the predecessor. Elaborates to @SNatRec base' step' scrut'@.
--
-- Γ ⊢ s ⇐ ℕ  Γ ⊢ t₁ ⇐ T  Γ ⊢ t₂ ⇐ ℕ → T → T
-- ───────────────────────────────────────── ℕ-Elim⇐
--           Γ ⊢ elim t₁ t₂ s ⇐ T
natElim :: Check -> Check -> Check -> Check
natElim zeroTac succTac scrutTac =
  Check $ \motive -> do
    scrutinee <- runCheck scrutTac NatTy
    base <- runCheck zeroTac motive
    step <- runCheck succTac (NatTy `FuncTy` (motive `FuncTy` motive))
    pure (SNatRec motive base step scrutinee)

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

newtype EvalM a = EvalM {runEvalM :: EvalEnv -> a}
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
  SSumCase t1 motive t2 t3 -> do
    t1' <- eval t1
    t2' <- eval t2
    t3' <- eval t3
    doSumCase t1' motive t2' t3'
  SAbsurd ty tm -> do
    tm' <- eval tm
    doSumAbsurd tm' ty
  SUnit -> pure VUnit
  STru -> pure VTru
  SFls -> pure VFls
  SIf p motive t1 t2 -> do
    p' <- eval p
    t1' <- eval t1
    t2' <- eval t2
    doIf p' motive t1' t2'
  SZero -> pure VZero
  SSucc tm -> VSucc <$> eval tm
  SNatRec motive base step n -> do
    n' <- eval n
    base' <- eval base
    step' <- eval step
    doNatRec n' motive base' step'

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

doSumCase :: Value -> Type -> Value -> Value -> EvalM Value
doSumCase (VInL v) _motive f _ = doApply f v
doSumCase (VInR v) _motive _ g = doApply g v
doSumCase (VNeutral (SumTy a b) neu) motive f g =
  pure $ VNeutral motive (pushFrame neu (VSumCase (FuncTy a motive) (FuncTy b motive) motive f g))
doSumCase _ _ _ _ = error "impossible case in doSumCase"

doSumAbsurd :: Value -> Type -> EvalM Value
doSumAbsurd (VNeutral _ neu) ty = pure $ VNeutral ty (pushFrame neu (VAbsurd ty))
doSumAbsurd _ _ = error "impossible case in doSumAbsurd"

doIf :: Value -> Type -> Value -> Value -> EvalM Value
doIf VTru _ p _ = pure p
doIf VFls _ _ q = pure q
doIf (VNeutral _ neu) motive t1 t2 = pure $ VNeutral motive (pushFrame neu (VIf motive t1 t2))
doIf _ _ _ _ = error "impossible case in doIf"

-- | Evaluate primitive recursion. At 'VZero' return the base case. At @VSucc n@
-- apply the step function to the predecessor @n@ and the recursive result on
-- @n@. At a neutral, produce a stuck 'VNatRec' frame.
doNatRec :: Value -> Type -> Value -> Value -> EvalM Value
doNatRec VZero _ z _f = pure z
doNatRec (VSucc n) motive z f = do
  hd <- doApply f n
  tl <- doNatRec n motive z f
  doApply hd tl
doNatRec (VNeutral _ neu) motive z f = do
  pure $ VNeutral motive $ pushFrame neu $ VNatRec motive z f
doNatRec _ _ _ _ = error "impossible case in doNatRec"

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
-- Booleans and naturals quote back to their syntax constructors ('STru',
-- 'SFls', 'SZero', 'SSucc').

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
quote _ _ VZero = pure SZero
quote l ty (VSucc tm) = SSucc <$> quote l ty tm
quote l _ (VNeutral _ neu) = quoteNeutral l neu
quote _ ty tm = error $ "impossible case in quote:\n" <> show ty <> "\n" <> show tm

quoteLevel :: Lvl -> Lvl -> Ix
quoteLevel (Lvl l) (Lvl x) = Ix (l - (x + 1))

quoteNeutral :: Lvl -> Neutral -> EvalM Syntax
quoteNeutral l Neutral {..} = foldM (quoteFrame l) (quoteHead l head) spine

quoteHead :: Lvl -> Head -> Syntax
quoteHead l (VVar lvl) = SVar (quoteLevel l lvl)
quoteHead _ (VHole ty) = SHole ty

quoteFrame :: Lvl -> Syntax -> Frame -> EvalM Syntax
quoteFrame l scrut = \case
  VApp ty arg -> SAp scrut <$> quote l ty arg
  VFst -> pure $ SFst scrut
  VSnd -> pure $ SSnd scrut
  VSumCase tyF tyG mot f g -> do
    f' <- quote l tyF f
    g' <- quote l tyG g
    pure $ SSumCase scrut mot f' g'
  VAbsurd ty -> pure $ SAbsurd ty scrut
  VIf motive p q -> liftA2 (SIf scrut motive) (quote l motive p) (quote l motive q)
  VNatRec motive base step -> do
    sbase <- quote l motive base
    sstep <- quote l (NatTy `FuncTy` (motive `FuncTy` motive)) step
    pure $ SNatRec motive sbase sstep scrut

bindVar :: Type -> Lvl -> (Value -> Lvl -> a) -> a
bindVar ty lvl f =
  let v = VNeutral ty $ Neutral (VVar lvl) Nil
   in f v $ incLevel lvl

--------------------------------------------------------------------------------
-- Main

run :: Term -> Either (Error, Holes) (RunResult Syntax Type Syntax, Holes)
run term =
  let action = do
        ((ty, syn), hs) <- listen (runSynth (synth term))
        ty' <- zonk ty
        hs' <- traverse zonk (getHoles hs)
        zonkedSyn <- zonkSyntax syn
        pure (ty', zonkedSyn, Holes hs')
   in case runTypecheckM action initMetas initEnv of
        ((Left err, holes), _metas) -> Left (err, holes)
        ((Right (type', syntax, holes), _unZonkedHoles), _metas) -> do
          let evalEnv = EvalEnv Nil
              result = flip runEvalM evalEnv $ do
                value <- eval syntax
                quote initLevel type' value
          pure (RunResult syntax type' result, holes)

main :: IO ()
main = do
  let test = runTest run
      testErr = runTestErr run

  putStrLn "=== System T ==="
  putStrLn ""

  -- Nat introduction
  section "Nat Introduction"
  test
    "Zero"
    (Anno NatTy Zero)
  test
    "Succ Zero (1)"
    (Anno NatTy (Succ Zero))
  test
    "Succ (Succ (Succ Zero)) (3)"
    (Anno NatTy (Succ (Succ (Succ Zero))))
  putStrLn ""

  -- NatRec — base case
  section "NatRec Base Case"
  test
    "natrec True (\\x.\\y. False) Zero ==> True"
    ( Anno
        BoolTy
        (NatRec Tru (Lam "x" (Lam "y" Fls)) Zero)
    )
  test
    "natrec Zero (\\x.\\y. Succ y) Zero ==> Zero"
    ( Anno
        NatTy
        (NatRec Zero (Lam "x" (Lam "y" (Succ (Var "y")))) Zero)
    )
  putStrLn ""

  -- NatRec — successor cases
  section "NatRec Successor Cases"
  test
    "natrec Zero (\\x.\\y. Succ y) (Succ Zero) ==> Succ Zero (add 1 0)"
    ( Anno
        NatTy
        (NatRec Zero (Lam "x" (Lam "y" (Succ (Var "y")))) (Succ Zero))
    )
  test
    "natrec Zero (\\x.\\y. Succ y) (Succ (Succ Zero)) ==> Succ (Succ Zero) (add 2 0)"
    ( Anno
        NatTy
        (NatRec Zero (Lam "x" (Lam "y" (Succ (Var "y")))) (Succ (Succ Zero)))
    )
  putStrLn ""

  -- NatRec — addition via lambda
  section "NatRec as Addition"
  test
    "add 2 1 ==> 3"
    ( Ap
        ( Ap
            ( Anno
                (NatTy `FuncTy` (NatTy `FuncTy` NatTy))
                (Lam "n" (Lam "m" (NatRec (Var "m") (Lam "x" (Lam "y" (Succ (Var "y")))) (Var "n"))))
            )
            (Anno NatTy (Succ (Succ Zero)))
        )
        (Anno NatTy (Succ Zero))
    )
  test
    "add 0 3 ==> 3"
    ( Ap
        ( Ap
            ( Anno
                (NatTy `FuncTy` (NatTy `FuncTy` NatTy))
                (Lam "n" (Lam "m" (NatRec (Var "m") (Lam "x" (Lam "y" (Succ (Var "y")))) (Var "n"))))
            )
            (Anno NatTy Zero)
        )
        (Anno NatTy (Succ (Succ (Succ Zero))))
    )
  putStrLn ""

  -- NatRec — using the predecessor argument
  section "NatRec Using Predecessor"
  test
    "isZero: natrec True (\\x.\\y. False) 0 ==> True"
    ( Anno
        BoolTy
        (NatRec Tru (Lam "_" (Lam "_" Fls)) Zero)
    )
  test
    "isZero: natrec True (\\x.\\y. False) 1 ==> False"
    ( Anno
        BoolTy
        (NatRec Tru (Lam "_" (Lam "_" Fls)) (Succ Zero))
    )
  test
    "isZero: natrec True (\\x.\\y. False) 3 ==> False"
    ( Anno
        BoolTy
        (NatRec Tru (Lam "_" (Lam "_" Fls)) (Succ (Succ (Succ Zero))))
    )
  putStrLn ""

  -- NatRec — step function uses predecessor
  section "NatRec Using Predecessor Argument"
  test
    "predecessor: natrec Zero (\\pred.\\acc. pred) 3 ==> 2"
    ( Anno
        NatTy
        (NatRec Zero (Lam "pred" (Lam "_" (Var "pred"))) (Succ (Succ (Succ Zero))))
    )
  test
    "predecessor: natrec Zero (\\pred.\\acc. pred) 1 ==> 0"
    ( Anno
        NatTy
        (NatRec Zero (Lam "pred" (Lam "_" (Var "pred"))) (Succ Zero))
    )
  test
    "predecessor of Zero: natrec Zero (\\pred.\\acc. pred) 0 ==> 0"
    ( Anno
        NatTy
        (NatRec Zero (Lam "pred" (Lam "_" (Var "pred"))) Zero)
    )
  putStrLn ""

  -- NatRec — factorial. The successor step multiplies the current value
  -- (Succ of the predecessor) by the recursive result, so it needs BOTH
  -- the predecessor and the recursion. A catamorphism could not write this
  -- without first reconstructing the predecessor. add and mult are
  -- themselves NatRecs, bound with let.
  --
  --   let add  = λm n. natrec n (λx y. Succ y) m            -- m + n
  --       mult = λm n. natrec Zero (λx y. add n y) m        -- m * n
  --       fact = λn. natrec (Succ Zero) (λx y. mult (Succ x) y) n
  --   in fact 3                                             -- ==> 6
  section "NatRec Factorial"
  test
    "fact 3 ==> 6"
    ( Anno
        NatTy
        ( Let
            "add"
            ( Anno
                (NatTy `FuncTy` (NatTy `FuncTy` NatTy))
                (Lam "m" (Lam "n" (NatRec (Var "n") (Lam "x" (Lam "y" (Succ (Var "y")))) (Var "m"))))
            )
            ( Let
                "mult"
                ( Anno
                    (NatTy `FuncTy` (NatTy `FuncTy` NatTy))
                    (Lam "m" (Lam "n" (NatRec Zero (Lam "x" (Lam "y" (Ap (Ap (Var "add") (Var "n")) (Var "y")))) (Var "m"))))
                )
                ( Let
                    "fact"
                    ( Anno
                        (NatTy `FuncTy` NatTy)
                        (Lam "n" (NatRec (Succ Zero) (Lam "x" (Lam "y" (Ap (Ap (Var "mult") (Succ (Var "x"))) (Var "y")))) (Var "n")))
                    )
                    (Ap (Var "fact") (Succ (Succ (Succ Zero))))
                )
            )
        )
    )
  putStrLn ""

  -- NatRec — returning non-Nat type
  section "NatRec with Non-Nat Motive"
  test
    "natrec () (\\x.\\y. ()) 2 ==> () (motive is Unit)"
    ( Anno
        UnitTy
        (NatRec Unit (Lam "_" (Lam "_" Unit)) (Succ (Succ Zero)))
    )
  test
    "natrec (True, False) (\\x.\\y. (False, True)) 1 ==> (False, True) (motive is Pair)"
    ( Anno
        (PairTy BoolTy BoolTy)
        (NatRec (Pair Tru Fls) (Lam "_" (Lam "_" (Pair Fls Tru))) (Succ Zero))
    )
  putStrLn ""

  -- NatRec stuck on a neutral scrutinee with a non-Nat motive. Under a
  -- lambda the scrutinee is neutral, so the recursor does not reduce and
  -- must be read back. This exercises the motive threaded through SNatRec.
  section "NatRec Stuck on Neutral (non-Nat motive)"
  -- Quoting the stuck recursor reads the base back at the motive Unit (not
  -- at Nat). Before the motive was threaded, this quoted () at Nat.
  test
    "\\n. natrec () (\\x y. ()) n  : Nat -> Unit"
    ( Anno
        (NatTy `FuncTy` UnitTy)
        (Lam "n" (NatRec Unit (Lam "x" (Lam "y" Unit)) (Var "n")))
    )
  -- The stuck recursor has a function motive (Nat -> Nat) and is then
  -- applied. doApply needs the neutral tagged with the motive, not Nat.
  test
    "\\n. (natrec (\\x. x) (\\p r. r) n) Zero  : Nat -> Nat"
    ( Anno
        (NatTy `FuncTy` NatTy)
        ( Lam
            "n"
            ( Ap
                ( Anno
                    (NatTy `FuncTy` NatTy)
                    (NatRec (Lam "x" (Var "x")) (Lam "p" (Lam "r" (Var "r"))) (Var "n"))
                )
                Zero
            )
        )
    )
  putStrLn ""

  -- Error cases
  section "Error Cases (expected failures)"
  testErr
    "Zero checked at Bool"
    (Anno BoolTy Zero)
  testErr
    "Succ Zero checked at Bool"
    (Anno BoolTy (Succ Zero))
  testErr
    "Succ True (non-Nat under Succ)"
    (Anno NatTy (Succ Tru))
  testErr
    "NatRec with non-Nat scrutinee"
    ( Anno
        BoolTy
        (NatRec Tru (Lam "_" (Lam "_" Fls)) Tru)
    )
  testErr
    "NatRec step function wrong type (expects Nat -> T -> T)"
    ( Anno
        BoolTy
        (NatRec Tru (Lam "_" Fls) Zero)
    )

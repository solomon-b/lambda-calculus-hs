{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- | TODO:
-- - Case on Records
-- - Case Trees
module Main where

--------------------------------------------------------------------------------

import Control.Arrow ((&&&))
import Control.Monad (foldM, forM, when)
import Control.Monad.Except (MonadError (..))
import Control.Monad.Identity
import Control.Monad.Reader (MonadReader (..), asks)
import Control.Monad.Trans.Except (ExceptT (..))
import Control.Monad.Trans.Reader (Reader, ReaderT (..))
import Control.Monad.Trans.Writer.Strict (WriterT (..))
import Control.Monad.Writer.Strict (MonadWriter (..))
import Data.Align (Semialign (..))
import Data.Foldable (find)
import Data.Map (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Scientific (Scientific)
import Data.String
import Data.These
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

alignWithM :: (Traversable f, Semialign f, Applicative m) => (These a b -> m c) -> f a -> f b -> m (f c)
alignWithM f as = traverse f . align as

--------------------------------------------------------------------------------
-- Types

-- | 'Term' represents the concrete syntax of our langage generated
-- from text by a parser.
data Term
  = Var Name
  | Lam Name Term
  | Ap Term Term
  | Pair Term Term
  | Fst Term
  | Snd Term
  | InL Term
  | InR Term
  | SumCase Term (Name, Term) (Name, Term)
  | Absurd Term
  | Unit
  | Tru
  | Fls
  | If Term Term Term
  | Record [(Name, Term)]
  | Get Name Term
  | Cnstr Name [Term]
  | CaseRec Term [(Name, [Name], Term)]
  | Integer Integer
  | Natural Integer
  | Real Scientific
  | Anno Type Term
  | Hole
  deriving stock (Show, Eq, Ord)

data Type
  = FuncTy Type Type
  | PairTy Type Type
  | UnitTy
  | SumTy Type Type
  | VoidTy
  | BoolTy
  | RecordTy [(Name, Type)]
  | MuTy Name Type
  | TVar Name
  | NaturalTy
  | IntegerTy
  | RealTy
  deriving stock (Show, Eq, Ord)

data DataConstructorSpec
  = Constr Name [Type]
  deriving stock (Show, Eq, Ord)

getCnstrName :: DataConstructorSpec -> Name
getCnstrName (Constr nm _) = nm

getCnstrTypes :: DataConstructorSpec -> [Type]
getCnstrTypes (Constr _ xs) = xs

data DataTypeSpec = DataTypeSpec Name [DataConstructorSpec]
  deriving stock (Show, Eq, Ord)

dataTypeSpecToMuTy :: DataTypeSpec -> Type
dataTypeSpecToMuTy (DataTypeSpec tyName cnstrs) =
  MuTy tyName $ foldSums $ fmap (foldProducts . getCnstrTypes) cnstrs
  where
    foldProducts [] = UnitTy
    foldProducts [x] = x
    foldProducts (x : xs) = PairTy x (foldProducts xs)

    foldSums [] = VoidTy
    foldSums [x] = x
    foldSums (x : xs) = SumTy x (foldSums xs)

-- | 'Syntax' is the internal abstract syntax of our language. We
-- elaborate 'Term' values into 'Syntax' during typechecking.
data Syntax
  = SVar Ix
  | SLam Name Syntax
  | SAp Syntax Syntax
  | SPair Syntax Syntax
  | SFst Syntax
  | SSnd Syntax
  | SInL Syntax
  | SInR Syntax
  | SSumCase Syntax Type Syntax Syntax
  | SSumAbsurd Type Syntax
  | SUnit
  | STru
  | SFls
  | SIf Syntax Syntax Syntax
  | SRecord [(Name, Syntax)]
  | SGet Name Syntax
  | SInteger Integer
  | SNatural Integer
  | SReal Scientific
  | SFold Syntax
  | SUnfold Syntax Type
  | SHole Type
  deriving stock (Show, Eq, Ord)

-- | 'Value' is the evaluated form of expressions in our language.
data Value
  = VNeutral Type Neutral
  | VLam Name Closure
  | VPair Value Value
  | VUnit
  | VInL Value
  | VInR Value
  | VTru
  | VFls
  | VRecord [(Name, Value)]
  | VInteger Integer
  | VNatural Integer
  | VReal Scientific
  | VFold Value
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

initLevel :: Lvl
initLevel = Lvl 0

incLevel :: Lvl -> Lvl
incLevel (Lvl n) = Lvl (1 + n)

newtype Name = Name {getName :: String}
  deriving newtype (Show, Eq, Ord, IsString)

data Neutral = Neutral {head :: Head, spine :: SnocList Frame}
  deriving stock (Show, Eq, Ord)

data Head
  = VVar Lvl
  | VHole Type
  deriving (Show, Eq, Ord)

data Frame
  = VApp Type Value
  | VFst
  | VSnd
  | VSumCase Type Type Type Value Value
  | VSumAbsurd Type
  | VIf Type Value Value
  | VGet Name
  | VUnfold Type
  deriving stock (Show, Eq, Ord)

pushFrame :: Neutral -> Frame -> Neutral
pushFrame Neutral {..} frame = Neutral {head = head, spine = Snoc spine frame}

data Closure = Closure {env :: SnocList Value, body :: Syntax}
  deriving stock (Show, Eq, Ord)

--------------------------------------------------------------------------------
-- Environment

data Cell = Cell
  { cellName :: Name,
    cellType :: Type,
    cellValue :: Value
  }
  deriving stock (Show, Eq, Ord)

data Env = Env
  { locals :: SnocList Value,
    localNames :: [Cell],
    size :: Int,
    -- | Holes encountered during typechecking
    holes :: [Type],
    -- | ADT Spec by Constructor Name
    adtConstructors :: Map Name DataTypeSpec
  }
  deriving stock (Show, Eq, Ord)

-- | We predefine a few ADTs here for demonstration purposes. In a
-- complete language these would be defined using 'data' declarations
-- in a module.
stockADTs :: Map Name DataTypeSpec
stockADTs =
  Map.fromList
    [ ("MaybeBool", DataTypeSpec "MaybeBool" [Constr "Nothing" [], Constr "Just" [BoolTy]]),
      ("ListBool", DataTypeSpec "ListBool" [Constr "Nil" [], Constr "Cons" [BoolTy, TVar "ListBool"]])
    ]

adtConstructorsMap :: Map Name DataTypeSpec
adtConstructorsMap = Map.fromList $ foldr (\d@(DataTypeSpec _ cs) acc -> fmap ((,d) . getCnstrName) cs <> acc) [] stockADTs

-- | Lookup a Data Constructor Spec from a Data Constructor Name.
lookupDataCnstrSpec :: Name -> ((Int, DataConstructorSpec) -> TypecheckM a) -> TypecheckM a
lookupDataCnstrSpec nm k =
  lookupDataTypeSpec nm $ \(DataTypeSpec tyName specs) ->
    case find (\(_, Constr nm' _) -> nm == nm') (zip [0 ..] specs) of
      Just cnstrSpec -> k cnstrSpec
      Nothing -> throwError $ TypeError $ "Data Constructor '" <> show nm <> "' does not match type: " <> show tyName

-- | Lookup the Data Constructor Spec from a Data Constructor Name.
lookupDataTypeSpec :: Name -> (DataTypeSpec -> TypecheckM a) -> TypecheckM a
lookupDataTypeSpec nm k =
  asks (Map.lookup nm . adtConstructors) >>= \case
    Just dataSpec -> k dataSpec
    Nothing -> throwError $ OutOfScopeError nm

-- | Lookup a Data Type Spec from a Data Type Name.
lookupDataTypeSpecByType :: Name -> (DataTypeSpec -> TypecheckM a) -> TypecheckM a
lookupDataTypeSpecByType tyName k = do
  cnstrs <- asks (Map.elems . adtConstructors)
  case find (\(DataTypeSpec tyName' _) -> tyName == tyName') cnstrs of
    Just dataSpec -> k dataSpec
    Nothing -> throwError $ OutOfScopeError tyName

initEnv :: Env
initEnv = Env Nil [] 0 mempty adtConstructorsMap

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
      holes = holes,
      adtConstructors = adtConstructors
    }

resolveCell :: Env -> Name -> Maybe Cell
resolveCell Env {..} bndr = find ((== bndr) . cellName) localNames

freshVar :: Env -> Type -> Value
freshVar Env {size} ty = VNeutral ty $ Neutral (VVar $ Lvl size) Nil

freshCell :: Env -> Name -> Type -> Cell
freshCell ctx name ty = Cell name ty (freshVar ctx ty)

substTy :: Name -> Type -> Type -> Type
substTy name replacement = go
  where
    go (TVar n) | n == name = replacement
    go (TVar n) = TVar n
    go (FuncTy a b) = FuncTy (go a) (go b)
    go (PairTy a b) = PairTy (go a) (go b)
    go (SumTy a b) = SumTy (go a) (go b)
    go (MuTy n t) | n == name = MuTy n t -- shadowed, don't recurse
    go (MuTy n t) = MuTy n (go t)
    go (RecordTy fields) = RecordTy (fmap (fmap go) fields)
    go t = t

-- | Unroll a μ-type by substituting the μ-type itself for the bound
-- variable in the body. For example:
--
-- unrollMuTy (μL. Unit + (Bool × L)) = Unit + (Bool × (μL. Unit + (Bool × L)))
unrollMuTy :: Type -> Type
unrollMuTy mu@(MuTy name body) = substTy name mu body
unrollMuTy ty = ty

-- | Weaken a 'Syntax' term by incrementing all free de Bruijn indices
-- by one. This is needed when pushing a term under an additional binder,
-- such as the lambdas introduced by 'buildCase' when elaborating n-ary
-- case expressions into nested binary sum eliminations.
weakenSyntax :: Syntax -> Syntax
weakenSyntax = go 0
  where
    go d (SVar (Ix i)) = SVar (Ix (if i >= d then i + 1 else i))
    go d (SLam n body) = SLam n (go (d + 1) body)
    go d (SAp a b) = SAp (go d a) (go d b)
    go d (SPair a b) = SPair (go d a) (go d b)
    go d (SFst a) = SFst (go d a)
    go d (SSnd a) = SSnd (go d a)
    go d (SInL a) = SInL (go d a)
    go d (SInR a) = SInR (go d a)
    go d (SSumCase s ty f g) = SSumCase (go d s) ty (go d f) (go d g)
    go d (SSumAbsurd ty s) = SSumAbsurd ty (go d s)
    go _ SUnit = SUnit
    go _ STru = STru
    go _ SFls = SFls
    go d (SIf p t f) = SIf (go d p) (go d t) (go d f)
    go d (SRecord fs) = SRecord (fmap (fmap (go d)) fs)
    go d (SGet n s) = SGet n (go d s)
    go _ (SInteger z) = SInteger z
    go _ (SNatural n) = SNatural n
    go _ (SReal r) = SReal r
    go d (SFold s) = SFold (go d s)
    go d (SUnfold s ty) = SUnfold (go d s) ty
    go _ (SHole ty) = SHole ty

--------------------------------------------------------------------------------
-- Typechecker

data Error
  = TypeError String
  | OutOfScopeError Name
  deriving (Show)

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
  Ap tm1 tm2 -> applyTactic (synth tm1) (check tm2)
  Fst tm -> fstTactic (synth tm)
  Snd tm -> sndTactic (synth tm)
  Anno ty tm -> annoTactic ty (check tm)
  Get name tm -> getTactic name (synth tm)
  Cnstr name tms -> constructorTactic name (fmap check tms)
  Hole -> Synth $ throwError $ TypeError "Cannot sythesize holes"
  tm -> Synth $ throwError $ TypeError $ "Cannot synthesize type for " <> show tm

check :: Term -> Check
check (Lam bndr body) = lamTactic bndr (check body)
check Unit = unitTactic
check (Pair tm1 tm2) = pairTactic (check tm1) (check tm2)
check (InL tm1) = inLTactic (check tm1)
check (InR tm2) = inRTactic (check tm2)
check (SumCase scrut (bndr1, t1) (bndr2, t2)) = sumCaseTactic (synth scrut) (check (Lam bndr1 t1)) (check (Lam bndr2 t2))
check (Absurd tm) = absurdTactic (synth tm)
check Hole = holeTactic
check (If tm1 tm2 tm3) = ifTactic (check tm1) (check tm2) (check tm3)
check Tru = trueTactic
check Fls = falseTactic
check (Integer z) = integerTactic z
check (Natural n) = naturalTactic n
check (Real r) = realTactic r
check (Record fields) = recordTactic (fmap (fmap (id &&& check)) fields)
check (CaseRec scrut cases) = caseRecTactic (synth scrut) (fmap (\(x, y, z) -> (x, check (foldr Lam z y))) cases)
check tm = subTactic (synth tm)

-- | Var Tactic
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

-- | Sub Tactic
--
-- Γ ⊢ e ⇒ A  A <∶ B
-- ──────────────── Sub⇐
--    Γ ⊢ e ⇐ B
subTactic :: Synth -> Check
subTactic (Synth synth) = Check $ \ty1 -> do
  (ty2, tm) <- synth
  if ty2 `isSubtypeOf` ty1
    then pure tm
    else throwError $ TypeError $ "Type '" <> show ty2 <> "' cannot be a subtype of type '" <> show ty1 <> "'"

-- | Anno Tactic
--
--    Γ ⊢ e ⇐ A
-- ─────────────── Anno⇒
-- Γ ⊢ (e : A) ⇒ A
annoTactic :: Type -> Check -> Synth
annoTactic ty (Check check) = Synth $ do
  tm <- check ty
  pure (ty, tm)

-- | Unit Introduction Tactic
--
-- ───────────── Unit⇐
-- Γ ⊢ () ⇐ Unit
unitTactic :: Check
unitTactic = Check $ \case
  UnitTy -> pure SUnit
  ty | isSubtypeOf UnitTy ty -> pure SUnit
  ty -> throwError $ TypeError $ "'Unit' cannot be a subtype of '" <> show ty <> "'"

-- | Lambda Introduction Tactic
--
--  Γ, x : A₁ ⊢ e ⇐ A₂
-- ──────────────────── LamIntro⇐
-- Γ ⊢ (λx.e) ⇐ A₁ → A₂
lamTactic :: Name -> Check -> Check
lamTactic bndr (Check bodyTac) = Check $ \case
  a `FuncTy` b -> do
    ctx <- ask
    let var = freshCell ctx bndr a
    fiber <- local (bindCell var) $ bodyTac b
    pure $ SLam bndr fiber
  ty -> throwError $ TypeError $ "Tried to introduce a lambda at a non-function type: " <> show ty

-- | Lambda Elination Tactic
--
-- Γ ⊢ e₁ ⇒ A → B  Γ ⊢ e₂ ⇐ A
-- ────────────────────────── LamElim⇐
--       Γ ⊢ e₁ e₂ ⇒ B
applyTactic :: Synth -> Check -> Synth
applyTactic (Synth funcTac) (Check argTac) =
  Synth $
    funcTac >>= \case
      (a `FuncTy` b, f) -> do
        arg <- argTac a
        pure (b, SAp f arg)
      (ty, _) -> throwError $ TypeError $ "Expected a function type but got " <> show ty

-- | Pair Introduction Tactic
--
-- Γ ⊢ a ⇐ A   Γ ⊢ b ⇐ B
-- ───────────────────── Pair⇐
--  Γ ⊢ (a , b) ⇐ A × B
pairTactic :: Check -> Check -> Check
pairTactic (Check checkFst) (Check checkSnd) = Check $ \case
  PairTy a b -> do
    tm1 <- checkFst a
    tm2 <- checkSnd b
    pure (SPair tm1 tm2)
  ty -> throwError $ TypeError $ "Couldn't match expected type Pair with actual type '" <> show ty <> "'"

-- | Pair Fst Elimination Tactic
--
-- Γ ⊢ (t₁ , t₂) ⇒ A × B
-- ───────────────────── Fst⇒
--       Γ ⊢ t₁ ⇒ A
fstTactic :: Synth -> Synth
fstTactic (Synth synth) =
  Synth $
    synth >>= \case
      (PairTy ty1 _ty2, SPair tm1 _tm2) -> pure (ty1, tm1)
      (ty, _) -> throwError $ TypeError $ "Couldn't match expected type Pair with actual type '" <> show ty <> "'"

-- | Pair Snd Elimination Tactic
--
-- Γ ⊢ (t₁ , t₂) ⇒ A × B
-- ───────────────────── Snd⇒
--       Γ ⊢ t₂ ⇒ A
sndTactic :: Synth -> Synth
sndTactic (Synth synth) =
  Synth $
    synth >>= \case
      (PairTy _ty1 ty2, SPair _tm1 tm2) -> pure (ty2, tm2)
      (ty, _) -> throwError $ TypeError $ "Couldn't match expected type Pair with actual type '" <> show ty <> "'"

-- | Fold Introduction Tactic
--
-- Generally the fold introduction would be a Check rule:
--
-- Γ ⊢ e ⇐ T[μα.T / α]
-- ──────────────────── Fold⇐
-- Γ ⊢ fold e ⇐ μα.T
--
-- However, because the fold is implicit in our surface syntax because the
-- constructor name tells us the 'DataTypeSpec', giving us the @MuTy@. This
-- means the tactic is able to know the type and can check the arguments then
-- synthesize the results.
--
-- Γ ⊢ Cᵢ is the i-th constructor of D    D elaborates to μα.T
-- T[μα.T / α] = S₁ + (S₂ + ... + Sₙ)    Γ ⊢ args ⇐ Sᵢ
-- ──────────────────────────────────────────────────────── Cnstr⇒
--                    Γ ⊢ Cᵢ args ⇒ μα.T
constructorTactic :: Name -> [Check] -> Synth
constructorTactic nm checks = Synth $
  lookupDataTypeSpec nm $ \dataTy@(DataTypeSpec _ cnstrs) ->
    lookupDataCnstrSpec nm $ \(i, _dataConstrSpec) -> do
      let muTy = dataTypeSpecToMuTy dataTy
          unrolled = unrollMuTy muTy
          branchTy = nthSumBranch i unrolled
      tm <- checkArgs checks branchTy
      pure (muTy, SFold $ injectAt i (length cnstrs) tm)
  where
    nthSumBranch :: Int -> Type -> Type
    nthSumBranch 0 (SumTy a _b) = a
    nthSumBranch 0 ty = ty
    nthSumBranch n (SumTy _a b) = nthSumBranch (n - 1) b
    nthSumBranch _ _ = error "impossible: constructor index out of bounds"

    checkArgs [] UnitTy = pure SUnit
    checkArgs [c] ty = runCheck c ty
    checkArgs (c : cs) (PairTy a b) = do
      x <- runCheck c a
      xs <- checkArgs cs b
      pure (SPair x xs)
    checkArgs _cs _ty = throwError $ TypeError $ "Argument count mismatch for constructor '" <> show nm <> "'"

    injectAt :: Int -> Int -> Syntax -> Syntax
    injectAt 0 1 tm = tm
    injectAt 0 _ tm = SInL tm
    injectAt i n tm = SInR (injectAt (i - 1) (n - 1) tm)

-- | InL Introduction Tactic
--
--      Γ ⊢ e ⇐ A
--  ───────────────── InL⇐
--  Γ ⊢ InL e ⇐ A + B
inLTactic :: Check -> Check
inLTactic (Check check) = Check $ \case
  SumTy a _b -> SInL <$> check a
  ty -> throwError $ TypeError $ "Expected a Sum type but got: " <> show ty

-- | InR Introduction Tactic
--
--  Γ ⊢ e ⇐ B
--  ──────────────── InR⇐
--  Γ ⊢ InR e ⇐ A + B
inRTactic :: Check -> Check
inRTactic (Check check) = Check $ \case
  SumTy _a b -> SInR <$> check b
  ty -> throwError $ TypeError $ "Expected a Sum type but got: " <> show ty

-- | Sum Case Elimination Tactic
--  Γ ⊢ e ⇒ A + B    Γ ⊢ f ⇐ A → C    Γ ⊢ g ⇐ B → C
--  ─────────────────────────────────────────────── SumCase⇐
--                Γ ⊢ SumCase e f g ⇐ C
sumCaseTactic :: Synth -> Check -> Check -> Check
sumCaseTactic (Synth synth) (Check checkT1) (Check checkT2) = Check $ \ty -> do
  (scrutTy, scrut) <- synth
  case scrutTy of
    SumTy a b -> do
      f <- checkT1 (FuncTy a ty)
      g <- checkT2 (FuncTy b ty)
      pure $ SSumCase scrut ty f g
    _ -> throwError $ TypeError $ "Expected a Sum type but got: " <> show scrutTy

-- | Void Elimination Tactic
--
--  Γ ⊢ e ⇒ Void
--  ─────────────── Absurd⇐
--  Γ ⊢ absurd e ⇐ C
absurdTactic :: Synth -> Check
absurdTactic (Synth synth) = Check $ \ty -> do
  (scrutTy, scrut) <- synth
  case scrutTy of
    VoidTy -> pure $ SSumAbsurd ty scrut
    _ -> throwError $ TypeError $ "Expected a Void but got: " <> show scrutTy

-- | Case-Rec Tactic
--
-- A typical Unfold tactic would look like:
--
--   Γ ⊢ e ⇒ μα.T
--  ──────────────────── Unfold
--  Γ ⊢ unfold e ⇒ T[μα.T / α]
--
-- However unfold never appears in our concrete syntax. It only appears as part
-- of our Case-Rec we do the unfold within the Case-Rec tactic:
--
--  Γ ⊢ e ⇒ μα.T    T[μα.T / α] = S₁ + (S₂ + ... + Sₙ)
--  Γ ⊢ fᵢ ⇐ Sᵢ → C   (for each i)
--  ──────────────────────────────────────── Case⇐
--  Γ ⊢ case e of C₁ → f₁ | ... | Cₙ → fₙ ⇐ C
caseRecTactic :: Synth -> [(Name, Check)] -> Check
caseRecTactic (Synth scrutinee) cases = Check $ \ty -> do
  (muTy, scrutinee) <- scrutinee
  case muTy of
    MuTy tyName _ -> do
      lookupDataTypeSpecByType tyName $ \(DataTypeSpec _ cnstrs) -> do
        let unrolled = unrollMuTy muTy
            casesMap = Map.fromList cases
            indexedCnstrs = zip [0 ..] cnstrs
        branches <- forM indexedCnstrs $ \(i, Constr name _) -> do
          case Map.lookup name casesMap of
            Just chk -> do
              let branchTy = nthSumBranch i unrolled
              tm <- runCheck chk (curryProductTy branchTy ty)
              pure (tm, branchTy)
            Nothing -> throwError $ TypeError $ "Missing case for constructor '" <> show name <> "'"
        when (Map.size casesMap > length cnstrs) $
          throwError $
            TypeError $
              "Extra case branches provided"

        pure $ buildCase (SUnfold scrutinee muTy) ty branches
    _ -> throwError $ TypeError $ "Expected a μ-type but got: " <> show muTy
  where
    nthSumBranch :: Int -> Type -> Type
    nthSumBranch 0 (SumTy a _b) = a
    nthSumBranch 0 ty = ty
    nthSumBranch n (SumTy _a b) = nthSumBranch (n - 1) b
    nthSumBranch _ _ = error "impossible: constructor index out of bounds"

    buildCase :: Syntax -> Type -> [(Syntax, Type)] -> Syntax
    buildCase scrut motive [] = SSumAbsurd motive scrut
    buildCase scrut _motive [(f, branchTy)] = uncurryApply f branchTy scrut
    buildCase scrut motive ((f, branchTy) : rest) =
      SSumCase
        scrut
        motive
        (SLam "_" (uncurryApply (weakenSyntax f) branchTy (SVar (Ix 0))))
        (SLam "_" (buildCase (SVar (Ix 0)) motive (fmap (\(s, t) -> (weakenSyntax s, t)) rest)))

    curryProductTy :: Type -> Type -> Type
    curryProductTy UnitTy motive = motive
    curryProductTy (PairTy a b) motive = FuncTy a (curryProductTy b motive)
    curryProductTy ty motive = FuncTy ty motive

    uncurryApply :: Syntax -> Type -> Syntax -> Syntax
    uncurryApply f UnitTy _scrut = f
    uncurryApply f (PairTy _a b) scrut = uncurryApply (SAp f (SFst scrut)) b (SSnd scrut)
    uncurryApply f _ty scrut = SAp f scrut

-- | Type Hole Tactic
--
--
-- ────────── Hole⇐
--  Γ ⊢ ? ⇐ A
holeTactic :: Check
holeTactic = Check $ \ty -> do
  tell (Holes [ty])
  pure (SHole ty)

-- | Bool-False Introduction Tactic
--
-- ──────────────── False⇐
-- Γ ⊢ False ⇐ Unit
falseTactic :: Check
falseTactic = Check $ \case
  BoolTy -> pure SFls
  ty | isSubtypeOf BoolTy ty -> pure SFls
  ty -> throwError $ TypeError $ "'Bool' cannot be a subtype of '" <> show ty <> "'"

-- | Bool-True Introduction Tactic
--
-- ──────────────── True⇐
-- Γ ⊢ True ⇐ Unit
trueTactic :: Check
trueTactic = Check $ \case
  BoolTy -> pure STru
  ty | isSubtypeOf BoolTy ty -> pure STru
  ty -> throwError $ TypeError $ "'Bool' cannot be a subtype of '" <> show ty <> "'"

-- | Bool Elimination Tactic
--
-- Γ ⊢ t₁ ⇐ Bool  Γ ⊢ t₂ ⇐ T  Γ ⊢ t₃ ⇐ T
-- ───────────────────────────────────── If⇐
--   Γ ⊢ If t₁ then t₂ else t₃ ⇐ Bool
ifTactic :: Check -> Check -> Check -> Check
ifTactic (Check checkT1) (Check checkT2) (Check checkT3) = Check $ \ty -> do
  tm1 <- checkT1 BoolTy
  tm2 <- checkT2 ty
  tm3 <- checkT3 ty
  pure (SIf tm1 tm2 tm3)

-- | Record Introduction Tactic
--
--         for each i  Γ ⊢ tᵢ ⇐ Tᵢ
-- ─────────────────────────────────────── Record⇐
-- Γ ⊢ { lᵢ = tᵢ} ⇐ { lᵢ : Tᵢ (i ∈ I..n) }
recordTactic :: [(Name, (Term, Check))] -> Check
recordTactic fields = Check $ \case
  RecordTy ty -> do
    fields' <-
      alignWithM
        ( \case
            These ty (_, chk) -> runCheck chk ty
            This ty -> throwError $ TypeError $ "Term is missing field of type: " <> show ty
            That (tm, _) -> throwError $ TypeError $ "Term has extra field: " <> show tm
        )
        (Map.fromList ty)
        (Map.fromList fields)
    pure (SRecord $ Map.toList fields')
  ty -> throwError $ TypeError $ "Expected a Record type but got: " <> show ty

-- | Record Elimination Tactic
--
-- Γ ⊢ t₁ ⇒ { lᵢ : Tᵢ (i ∈ I..n) }
-- ─────────────────────────────── Get⇒
--       Γ ⊢ Get lⱼ t₁ ⇒ Tⱼ
getTactic :: Name -> Synth -> Synth
getTactic name (Synth fieldTac) =
  Synth $
    fieldTac >>= \case
      (RecordTy fields, tm) ->
        case lookup name fields of
          Just ty -> pure (ty, SGet name tm)
          Nothing -> throwError $ TypeError $ "Record does not contain a field called " <> show name
      (ty, _) -> throwError $ TypeError $ "Expected a record type but got " <> show ty

-- | Integer Introduction Tactic
--
-- ──────── ℤ⇐
-- Γ ⊢ z ⇐  ℤ
integerTactic :: Integer -> Check
integerTactic z = Check $ \case
  IntegerTy -> pure (SInteger z)
  ty | isSubtypeOf IntegerTy ty -> pure (SInteger z)
  ty -> throwError $ TypeError $ "'Integer' cannot be a subtype of '" <> show ty <> "'"

-- | Natural Introduction Tactic
--
-- ───────── ℕ⇐
-- Γ ⊢ n ⇐ ℕ
naturalTactic :: Integer -> Check
naturalTactic n = Check $ \case
  NaturalTy ->
    if n >= 0
      then pure (SNatural n)
      else throwError $ TypeError "Naturals must be greater then or equal to zero."
  ty | isSubtypeOf NaturalTy ty -> pure (SNatural n)
  ty -> throwError $ TypeError $ "'Natural' cannot be a subtype of '" <> show ty <> "'"

-- | Real Introduction Tactic
--
-- ───────── ℝ⇐
-- Γ ⊢ r ⇐ ℝ
realTactic :: Scientific -> Check
realTactic r = Check $ \case
  RealTy -> pure (SReal r)
  ty | isSubtypeOf RealTy ty -> pure (SReal r)
  ty -> throwError $ TypeError $ "'Real' cannot be a subtype of '" <> show ty <> "'"

--------------------------------------------------------------------------------
-- Subsumption

-- | The subtyping relationship T₁ <: T₂ can be read as "T₁ is a
-- subtype of T₂". It can be understood as stating that anywhere a T₂
-- can be used, we can use a T₁.
isSubtypeOf :: Type -> Type -> Bool
isSubtypeOf s@RecordTy {} t@RecordTy {} = recordSubtypeTactic s t
isSubtypeOf s@FuncTy {} t@FuncTy {} = functionSubtypeTactic s t
isSubtypeOf NaturalTy IntegerTy = True
isSubtypeOf NaturalTy RealTy = True
isSubtypeOf IntegerTy RealTy = True
isSubtypeOf super sub = super == sub

-- | Record Depth Subtyping
--
-- Any field of a record can be replaced by its subtype. Since any
-- operation supported for a field in the supertype is supported for
-- its subtype, any operation feasible on the record supertype is
-- supported by the record subtype.
--
-- For example:
--
-- { foo : ℕ } <: { foo : ℤ }
--
-- We can write our typing rule as:
--
--              Sᵢ <: Tᵢ (i ∈ 1..n)
-- ──────────────────────────────────────────────── RecordDepth
-- { lᵢ : Sᵢ (i ∈ I..n) } <: { lᵢ : Tᵢ (i ∈ I..n) }
--
-- TODO: Record Width Subtyping:
-- https://en.wikipedia.org/wiki/Subtyping#Width_and_depth_subtyping
--
-- eg.,:
-- { foo :: Nat, bar :: Bool } <: { foo :: Nat }
-- ({ foo :: Nat, bar :: Bool} → Nat) <: ({ foo :: Nat } → Nat)
recordSubtypeTactic :: Type -> Type -> Bool
recordSubtypeTactic (RecordTy s) (RecordTy t) =
  let s' = Map.fromList s
      t' = Map.fromList t
   in Map.isSubmapOfBy isSubtypeOf t' s'
recordSubtypeTactic _ _ = error "impossible case in rec"

-- | Function Subtyping
--
-- A subtype of T₁ → T₂ is any type S₁ → S₂ such that T₁ <: S₁ and S₂ <: T₂.
--
-- For example:
--
-- (ℤ → ℕ) <: (ℕ → ℤ)
--
-- These feels backwards at first glance, but the received parameter
-- T₁/S₁ is contravariant. This reverses the subtyping relationship.
--
-- Another way of stating the example above is that you can replace a
-- function ℕ → ℤ with a function ℤ → ℕ.
--
-- This works because any ℕ you would have applied to the supertype
-- function is also an ℤ which can also be applied to the subtype
-- function.
--
-- Likewise the ℕ produced by the subtype function is also a ℤ and
-- thus satisfies the super type's return param.
--
-- Thus our typing rule for function subtyping is:
--
-- T₁ <: S₁  S₂ <: T₂
-- ────────────────── Func-Sub
-- S₁ → S₂ <: T₁ → T₂
functionSubtypeTactic :: Type -> Type -> Bool
functionSubtypeTactic (s1 `FuncTy` s2) (t1 `FuncTy` t2) =
  t1 `isSubtypeOf` s1 && s2 `isSubtypeOf` t2
functionSubtypeTactic _ _ = error "impossible case in functionSubTypeTactic"

--------------------------------------------------------------------------------
-- Evaluator

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
  SPair tm1 tm2 -> do
    tm1' <- eval tm1
    tm2' <- eval tm2
    pure $ VPair tm1' tm2'
  SFst tm -> eval tm >>= doFst
  SSnd tm -> eval tm >>= doSnd
  SInL tm -> eval tm >>= pure . VInL
  SInR tm -> eval tm >>= pure . VInR
  SSumCase t1 motive t2 t3 -> do
    t1' <- eval t1
    t2' <- eval t2
    t3' <- eval t3
    doSumCase t1' motive t2' t3'
  SSumAbsurd ty tm -> do
    tm' <- eval tm
    doSumAbsurd tm' ty
  SUnit -> pure VUnit
  STru -> pure VTru
  SFls -> pure VFls
  SIf p t1 t2 -> do
    p' <- eval p
    t1' <- eval t1
    t2' <- eval t2
    doIf p' t1' t2'
  SRecord fields -> doRecord fields
  SGet name tm -> eval tm >>= doGet name
  SInteger z -> pure $ VInteger z
  SNatural n -> pure $ VNatural n
  SReal r -> pure $ VReal r
  SFold tm -> VFold <$> eval tm
  SUnfold tm muTy -> eval tm >>= doUnfold muTy
  SHole ty -> pure $ VNeutral ty (Neutral (VHole ty) Nil)

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

doSumCase :: Value -> Type -> Value -> Value -> EvalM Value
doSumCase (VInL v) _motive f _ = doApply f v
doSumCase (VInR v) _motive _ g = doApply g v
doSumCase (VNeutral (SumTy a b) neu) motive f g =
  pure $ VNeutral motive (pushFrame neu (VSumCase (FuncTy a motive) (FuncTy b motive) motive f g))
doSumCase _ _ _ _ = error "impossible case in doSumCase"

doSumAbsurd :: Value -> Type -> EvalM Value
doSumAbsurd (VNeutral _ neu) ty = pure $ VNeutral ty (pushFrame neu (VSumAbsurd ty))
doSumAbsurd _ _ = error "impossible case in doSumAbsurd"

doIf :: Value -> Value -> Value -> EvalM Value
doIf VTru t1 _ = pure t1
doIf VFls _ t2 = pure t2
doIf (VNeutral ty neu) t1 t2 = pure $ VNeutral BoolTy (pushFrame neu (VIf ty t1 t2))
doIf _ _ _ = error "impossible case in doIf"

doRecord :: [(Name, Syntax)] -> EvalM Value
doRecord fields = VRecord <$> traverse (traverse eval) fields

doGet :: Name -> Value -> EvalM Value
doGet name (VRecord fields) =
  case lookup name fields of
    Nothing -> error "impossible case in doGet lookup"
    Just field -> pure field
doGet _ _ = error "impossible case in doGet"

doUnfold :: Type -> Value -> EvalM Value
doUnfold _ (VFold v) = pure v
doUnfold muTy (VNeutral _ neu) = pure $ VNeutral (unrollMuTy muTy) (pushFrame neu (VUnfold muTy))
doUnfold _ _ = error "impossible case in doUnfold"

instantiateClosure :: Closure -> Value -> EvalM Value
instantiateClosure (Closure env body) v = local (const $ Snoc env v) $ eval body

--------------------------------------------------------------------------------
-- Quoting

quote :: Lvl -> Type -> Value -> EvalM Syntax
quote l (FuncTy ty1 ty2) (VLam bndr clo@(Closure _env _body)) = do
  body <- bindVar ty1 l $ \v l' -> do
    clo <- instantiateClosure clo v
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
quote l _ (VNeutral _ neu) = quoteNeutral l neu
quote _ _ VUnit = pure SUnit
quote _ _ VTru = pure STru
quote _ _ VFls = pure SFls
quote l ty (VRecord fields) = SRecord <$> traverse (traverse (quote l ty)) fields
quote _ _ (VNatural n) = pure $ SNatural n
quote _ _ (VInteger z) = pure $ SInteger z
quote _ _ (VReal r) = pure $ SReal r
quote l (MuTy name body) (VFold v) = SFold <$> quote l (unrollMuTy (MuTy name body)) v
quote _ ty tm = error $ "impossible case in quote:\n" <> show ty <> "\n" <> show tm

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
  VSumCase tyF tyG mot f g -> do
    f' <- quote l tyF f
    g' <- quote l tyG g
    pure $ SSumCase tm mot f' g'
  VSumAbsurd ty -> pure $ SSumAbsurd ty tm
  VIf ty t1 t2 -> liftA2 (SIf tm) (quote l ty t1) (quote l ty t2)
  -- NOTE: This never get constructed. Do I need them in STLC?
  VGet name -> pure $ SGet name tm
  VUnfold ty -> pure $ SUnfold tm ty

bindVar :: Type -> Lvl -> (Value -> Lvl -> a) -> a
bindVar ty lvl f =
  let v = VNeutral ty $ Neutral (VVar lvl) Nil
   in f v $ incLevel lvl

--------------------------------------------------------------------------------
-- Main

run :: Term -> Either (Error, Holes) (RunResult Type Syntax, Holes)
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

  putStrLn "=== Iso-Recursive Types ==="
  putStrLn ""

  -- Construction tests
  section "Construction"
  test
    "Nil"
    (Cnstr "Nil" [])
  test
    "Cons True Nil"
    (Cnstr "Cons" [Tru, Cnstr "Nil" []])
  test
    "Cons True (Cons False Nil)"
    (Cnstr "Cons" [Tru, Cnstr "Cons" [Fls, Cnstr "Nil" []]])
  test
    "Nothing"
    (Cnstr "Nothing" [])
  test
    "Just True"
    (Cnstr "Just" [Tru])
  putStrLn ""

  -- Case elimination tests
  section "Case Elimination"
  test
    "case Nil of Nil -> True | Cons x xs -> False  ==>  True"
    ( Anno
        BoolTy
        ( CaseRec
            (Cnstr "Nil" [])
            [("Nil", [], Tru), ("Cons", ["x", "xs"], Fls)]
        )
    )
  test
    "case (Cons True Nil) of Nil -> False | Cons x xs -> x  ==>  True"
    ( Anno
        BoolTy
        ( CaseRec
            (Cnstr "Cons" [Tru, Cnstr "Nil" []])
            [("Nil", [], Fls), ("Cons", ["x", "xs"], Var "x")]
        )
    )
  test
    "case (Cons False Nil) of Nil -> True | Cons x xs -> x  ==>  False"
    ( Anno
        BoolTy
        ( CaseRec
            (Cnstr "Cons" [Fls, Cnstr "Nil" []])
            [("Nil", [], Tru), ("Cons", ["x", "xs"], Var "x")]
        )
    )
  test
    "case Nothing of Nothing -> True | Just x -> x  ==>  True"
    ( Anno
        BoolTy
        ( CaseRec
            (Cnstr "Nothing" [])
            [("Nothing", [], Tru), ("Just", ["x"], Var "x")]
        )
    )
  test
    "case (Just False) of Nothing -> True | Just x -> x  ==>  False"
    ( Anno
        BoolTy
        ( CaseRec
            (Cnstr "Just" [Fls])
            [("Nothing", [], Tru), ("Just", ["x"], Var "x")]
        )
    )
  putStrLn ""

  -- Nested case / recursive structure tests
  section "Nested / Recursive"
  let listBoolTy = dataTypeSpecToMuTy (DataTypeSpec "ListBool" [Constr "Nil" [], Constr "Cons" [BoolTy, TVar "ListBool"]])
  test
    "case (case (Cons True (Cons False Nil)) of Nil -> Nil | Cons x xs -> xs) of Nil -> True | Cons x xs -> x  ==>  False"
    ( Anno
        BoolTy
        ( CaseRec
            ( Anno
                listBoolTy
                ( CaseRec
                    (Cnstr "Cons" [Tru, Cnstr "Cons" [Fls, Cnstr "Nil" []]])
                    [("Nil", [], Cnstr "Nil" []), ("Cons", ["x", "xs"], Var "xs")]
                )
            )
            [("Nil", [], Tru), ("Cons", ["x", "xs"], Var "x")]
        )
    )
  test
    "case Nil of Nil -> Nil | Cons x xs -> xs  ==>  Nil (recursive return type)"
    ( Anno
        listBoolTy
        ( CaseRec
            (Cnstr "Nil" [])
            [("Nil", [], Cnstr "Nil" []), ("Cons", ["x", "xs"], Var "xs")]
        )
    )
  putStrLn ""

  -- Holes
  section "Holes"
  test
    "Cons ? Nil  (hole in constructor arg)"
    (Cnstr "Cons" [Hole, Cnstr "Nil" []])
  putStrLn ""

  -- Error cases
  section "Error Cases (expected failures)"
  testErr
    "Too many args: Cons True False Nil"
    (Cnstr "Cons" [Tru, Fls, Cnstr "Nil" []])
  testErr
    "Too few args: Cons True"
    (Cnstr "Cons" [Tru])
  testErr
    "Missing case branch"
    ( Anno
        BoolTy
        ( CaseRec
            (Cnstr "Nil" [])
            [("Nil", [], Tru)]
        )
    )
  testErr
    "Extra case branch"
    ( Anno
        BoolTy
        ( CaseRec
            (Cnstr "Nil" [])
            [("Nil", [], Tru), ("Cons", ["x", "xs"], Fls), ("Bogus", [], Fls)]
        )
    )
  testErr
    "Case on non-mu type"
    ( Anno
        BoolTy
        (CaseRec (Anno BoolTy Tru) [("Nil", [], Fls)])
    )
  testErr
    "Unknown constructor"
    (Cnstr "Bogus" [])

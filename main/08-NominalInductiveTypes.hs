{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- | TODO:
-- - Case on Records
-- - Case Trees
module Main where

--------------------------------------------------------------------------------

import Control.Applicative (liftA2)
import Control.Arrow ((&&&))
import Control.Monad.Except (MonadError (..))
import Control.Monad.Identity
import Control.Monad.Reader (MonadReader (..), asks)
import Control.Monad.Trans.Except (ExceptT (..))
import Control.Monad.Trans.Reader (Reader, ReaderT (..))
import Control.Monad.Trans.Writer.Strict (WriterT (..))
import Control.Monad.Writer.Strict (MonadWriter (..))
import Data.Align (Semialign (..))
import Data.Foldable (find, foldl')
import Data.Map (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Scientific (Scientific)
import Data.String
import Data.These
import Debug.Trace

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
  | Unit
  | Tru
  | Fls
  | If Term Term Term
  | Record [(Name, Term)]
  | Get Name Term
  | Cnstr Name [Term]
  | Case Term [(Name, [Name], Term)]
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
  | BoolTy
  | RecordTy [(Name, Type)]
  | AdtTy Name
  | NaturalTy
  | IntegerTy
  | RealTy
  deriving stock (Show, Eq, Ord)

data ArgSpec
  = Term Type
  | -- NOTE If we had type operators then this would be
    --  | Rec -- [Type]
    Rec
  deriving stock (Show, Eq, Ord)

data ConstrSpec
  = Constr Name [ArgSpec]
  deriving stock (Show, Eq, Ord)

getCnstrName :: ConstrSpec -> Name
getCnstrName (Constr nm _) = nm

data DataSpec
  = -- If we had type variables then this would be:
    -- Data Name [Name] [ConstrSpec]
    -- If we had Kinds then this would be:
    -- Data Name [Kind] [ConstrSpec]
    -- If we had MLTT then this would be:
    -- Data Name [Term] [ConstrSpec]
    Data Name [ConstrSpec]
  deriving stock (Show, Eq, Ord)

-- | 'Syntax' is the internal abstract syntax of our language. We
-- elaborate 'Term' values into 'Syntax' during typechecking.
data Syntax
  = SVar Ix
  | SLam Name Syntax
  | SAp Syntax Syntax
  | SPair Syntax Syntax
  | SFst Syntax
  | SSnd Syntax
  | SUnit
  | STru
  | SFls
  | SIf Syntax Syntax Syntax
  | SRecord [(Name, Syntax)]
  | SGet Name Syntax
  | SInteger Integer
  | SNatural Integer
  | SReal Scientific
  | SCnstr Name [Syntax]
  | SCase Syntax [(Name, Syntax)]
  | SHole Type
  deriving stock (Show, Eq, Ord)

-- | 'Value' is the evaluated form of expressions in our language.
data Value
  = VNeutral Type Neutral
  | VLam Name Closure
  | VPair Value Value
  | VUnit
  | VTru
  | VFls
  | VRecord [(Name, Value)]
  | VInteger Integer
  | VNatural Integer
  | VReal Scientific
  | VCnstr Name [Value]
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
  | VIf Type Value Value
  | VGet Name
  | VCase Type [(Name, Value)]
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
    holes :: [Type],
    -- | ADT Spec by Type Name
    adtTypes :: Map Name DataSpec,
    -- | ADT Spec by Constructor Name
    adtConstructors :: Map Name DataSpec
  }
  deriving stock (Show, Eq, Ord)

-- | We predefine a few ADTs here for demonstration purposes. In a
-- complete langauge these would be defined using 'data' declarations.
stockADTs :: Map Name DataSpec
stockADTs =
  Map.fromList
    [ ("MaybeBool", Data "MaybeBool" [Constr "Nothing" [], Constr "Just" [Term BoolTy]]),
      ("ListBool", Data "ListBool" [Constr "Nil" [], Constr "Cons" [Term BoolTy, Rec]])
    ]

adtConstructorsMap :: Map Name DataSpec
adtConstructorsMap = Map.fromList $ foldr (\d@(Data _ cs) acc -> fmap ((,d) . getCnstrName) cs <> acc) [] stockADTs

-- | Lookup an ADT Spec in the global context.
lookupDataSpec :: Name -> (DataSpec -> TypecheckM a) -> TypecheckM a
lookupDataSpec tyName k =
  asks (Map.lookup tyName . adtTypes) >>= \case
    Just dataSpec -> k dataSpec
    Nothing -> throwError $ OutOfScopeError tyName

-- | Lookup a Data Constructor Spec from a given ADT Spec.
lookupDataCnstr :: Name -> DataSpec -> (ConstrSpec -> TypecheckM a) -> TypecheckM a
lookupDataCnstr cnstrName (Data tyName specs) k =
  case find (\(Constr nm _) -> nm == cnstrName) specs of
    Just cnstrSpec -> k cnstrSpec
    Nothing -> throwError $ TypeError $ "Data Constructor '" <> show cnstrName <> "' does not match type: " <> show tyName

lookupDataCnstr' :: Name -> TypecheckM DataSpec
lookupDataCnstr' nm =
  asks (Map.lookup nm . adtConstructors) >>= \case
    Just dataSpec -> pure dataSpec
    Nothing -> throwError $ OutOfScopeError nm

initEnv :: Env
initEnv = Env Nil [] 0 mempty stockADTs adtConstructorsMap

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
      adtTypes = adtTypes,
      adtConstructors = adtConstructors
    }

bindCells :: [Cell] -> Env -> Env
bindCells cells env = foldr bindCell env cells

resolveCell :: Env -> Name -> Maybe Cell
resolveCell Env {..} bndr = find ((== bndr) . cellName) localNames

freshVar :: Env -> Type -> Value
freshVar Env {size} ty = VNeutral ty $ Neutral (VVar $ Lvl size) Nil

freshCell :: Env -> Name -> Type -> Cell
freshCell ctx name ty = Cell name ty (freshVar ctx ty)

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
  Hole -> Synth $ throwError $ TypeError "Cannot sythesize holes"
  tm -> Synth $ throwError $ TypeError $ "Cannot synthesize type for " <> show tm

check :: Term -> Check
check (Lam bndr body) = lamTactic bndr (check body)
check Unit = unitTactic
check (Pair tm1 tm2) = pairTactic (check tm1) (check tm2)
check Hole = holeTactic
check (If tm1 tm2 tm3) = ifTactic (check tm1) (check tm2) (check tm3)
check Tru = trueTactic
check Fls = falseTactic
check (Integer z) = integerTactic z
check (Natural n) = naturalTactic n
check (Real r) = realTactic r
check (Record fields) = recordTactic (fmap (fmap (id &&& check)) fields)
check (Cnstr nm args) = constructorTactic nm (fmap check args)
check (Case scrut cases) = caseTactic (synth scrut) (fmap (\(x, y, z) -> (x, check (foldr Lam z y))) cases)
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

-- | ADT Introduction Tactic
--
-- Γ ⊢ 𝐶 : T₁ → ... → Tₙ → T   Γ ⊢ 𝑡ᵢ ⇐ Tᵢ (i ∈ 1 ... n)
-- ──────────────────────────────────────────────────── Cnstr⇐
--                   Γ ⊢ 𝐶 𝑡₁ ... 𝑡ₙ ⇐ T
constructorTactic :: Name -> [Check] -> Check
constructorTactic nm chks = Check $ \case
  ty@AdtTy {} -> runCheck (constructorFullTactic nm chks) ty
  ty@FuncTy {} -> runCheck (constructorPartialTactic nm chks) ty
  ty -> throwError $ TypeError $ "Expected '" <> show (AdtTy nm) <> "', but recieved '" <> show ty <> "'"

constructorFullTactic :: Name -> [Check] -> Check
constructorFullTactic nm chks = Check $ \case
  AdtTy tyName -> do
    lookupDataSpec tyName $ \dataSpec ->
      lookupDataCnstr nm dataSpec $ \cnstrSpec ->
        case extractParamsFromSpec tyName cnstrSpec of
          Just (cnstrName, params) -> do
            let plength = length params
            let clength = length chks
            if
                | clength > plength ->
                    throwError $ TypeError $ "Data Constructor '" <> show cnstrName <> "' is applied to " <> show clength <> " value arguments, but it's type only expects " <> show plength
                | clength < plength ->
                    throwError $ TypeError $ "Data Constructor '" <> show cnstrName <> "' is applied to too few arguments"
                | otherwise -> do
                    args <- zipWithM runCheck chks params
                    pure $ SCnstr nm args
          Nothing -> error "impossible case in constructorFullTactic"
  _ -> error "impossible case in constructorFullTactic"

constructorPartialTactic :: Name -> [Check] -> Check
constructorPartialTactic nm chks = Check $ \case
  ty@FuncTy {} ->
    lookupDataCnstr' nm >>= \dataSpec@(Data tyName _) ->
      case decomposeFunction ty of
        (AdtTy tyName', unappliedParamTypes) | isSubtypeOf (AdtTy tyName) (AdtTy tyName') -> do
          lookupDataCnstr nm dataSpec $ \cnstrSpec ->
            case extractParamsFromSpec tyName cnstrSpec of
              Just (cnstrName, params) -> do
                let unappliedParamTypesL = length unappliedParamTypes
                if
                    | length params == unappliedParamTypesL + length chks -> do
                        args <- zipWithM runCheck chks params
                        pure $ applyParams cnstrName args unappliedParamTypesL
                    | length params > unappliedParamTypesL + length chks ->
                        throwError $ TypeError $ "Data Constructor'" <> show nm <> "' is applied to too few arguments"
                    | otherwise ->
                        throwError $ TypeError $ "Data Constructor'" <> show nm <> "' is applied to " <> show (length chks) <> " value arguments, but it's type only expects " <> show unappliedParamTypesL
              Nothing -> error "impossible case in constructorPartialTactic"
        (ty, unappliedParamTypes) | isSubtypeOf (AdtTy tyName) ty -> do
          lookupDataCnstr nm dataSpec $ \cnstrSpec ->
            case extractParamsFromSpec tyName cnstrSpec of
              Just (cnstrName, params) -> do
                let unappliedParamTypesL = length unappliedParamTypes
                if
                    | length params == unappliedParamTypesL + length chks -> do
                        args <- zipWithM runCheck chks params
                        pure $ applyParams cnstrName args unappliedParamTypesL
                    | length params > unappliedParamTypesL + length chks ->
                        throwError $ TypeError $ "Data Constructor'" <> show nm <> "' is applied to too few arguments"
                    | otherwise ->
                        throwError $ TypeError $ "Data Constructor'" <> show nm <> "' is applied to " <> show (length chks) <> " value arguments, but it's type only expects " <> show unappliedParamTypesL
              Nothing -> error "impossible case in constructorPartialTactic"
        (ty@AdtTy {}, _unappliedParamTypes) -> throwError $ TypeError $ "'" <> show tyName <> "' cannot be a subtype of '" <> show ty <> "'"
        (ty, _unappliedParamTypes) -> throwError $ TypeError $ "'" <> show tyName <> "' cannot be a subtype of '" <> show ty <> "'"
  _ -> error "impossible case in constructorPartialTactic"

-- | Eta expand around a data constructor with the missing params
applyParams :: Name -> [Syntax] -> Int -> Syntax
applyParams cnstrName args missing =
  let vars = fmap (SVar . Ix) [0 .. missing - 1]
   in foldl' (\acc _ -> SLam "_" acc) (SCnstr cnstrName (args <> vars)) vars

extractParamsFromSpec :: Name -> ConstrSpec -> Maybe (Name, [Type])
extractParamsFromSpec tyName cnstrSpec = decomposeFunctionAdt (constrType tyName cnstrSpec)

-- | Build a function type from a 'ConstrSpec'
constrType :: Name -> ConstrSpec -> Type
constrType tyName (Constr _nm []) = AdtTy tyName
constrType tyName (Constr nm (Term x : xs)) = FuncTy x $ constrType tyName (Constr nm xs)
constrType tyName (Constr nm (Rec : xs)) = FuncTy (AdtTy tyName) $ constrType tyName (Constr nm xs)

-- | Decompose a function into its return type and a list of its args.
decomposeFunction :: Type -> (Type, [Type])
decomposeFunction (FuncTy a b) = (a :) <$> decomposeFunction b
decomposeFunction ty = (ty, [])

-- | Decompose a function and fail if the return type is not an ADT.
decomposeFunctionAdt :: Type -> Maybe (Name, [Type])
decomposeFunctionAdt ty =
  case decomposeFunction ty of
    (AdtTy tyName, args) -> Just (tyName, args)
    _ -> Nothing

-- | ADT Elimination Tactic
--
-- The core idea is that given an ADT:
--
-- data ListBool = Nil | Cons Bool ListBool
--
-- We want to build an eliminator function:
--
-- list-bool-elim : A -> (Bool -> A -> A) -> ListBool -> A
--
-- NOTE: The 'Nil' eliminator ought to be '() -> A' but that is
-- isomorphic to 'A' so we can simplify it.
--
-- The 'DataSpec' for ListBool is:
--
-- Data "ListBool" [Constr "Nil" [], Constr "Just" [Term BoolTy, Rec []]]
--
-- From this we derive the recursion principle for our eliminator. The
-- elminator receives one function per Data Constructor which returns
-- our goal type 'A'. The parameters on the constructor become
-- parameters on the function where recursive references are replaced
-- by the goal type:
--
--                   ∨---- (Term BoolTy, Rec []])
-- bool-elim : A -> (Bool -> A -> A) -> ListBool -> A
--             ∧---- Constr "Nil" []
--
-- The goal type 'A' is the type of the case pattern bodies.
--
-- For example:
--
-- case xs of
--   | Nil -> false
--   | Cons b xs -> b
--
-- bool-elim : (Bool) -> (Bool -> Bool -> Bool) -> ListBool -> Bool
--
-- For the 'Nil' case we check the body against 'Bool' and for
-- the 'Cons' case we check the body against '(Bool -> Bool -> Bool)'
mkConstrEliminator :: Name -> Type -> ConstrSpec -> (Name, Type)
mkConstrEliminator tyName motiveTy (Constr nm args) =
  (nm, foldr (flip $ \acc -> \case Term ty -> ty `FuncTy` acc; Rec -> AdtTy tyName `FuncTy` acc) motiveTy args)

mkEliminator :: Type -> DataSpec -> [(Name, Type)]
mkEliminator motiveTy (Data tyName specs) = fmap (mkConstrEliminator tyName motiveTy) specs

caseTactic :: Synth -> [(Name, Check)] -> Check
caseTactic scrut cases = Check $ \motive -> do
  runSynth scrut >>= \case
    (AdtTy tyName, scrut'@SCnstr {}) ->
      lookupDataSpec tyName $ \dataSpec -> do
        let eliminators = Map.fromList $ traceShowId $ mkEliminator motive dataSpec
            checks = Map.fromList cases
            alignCases = \case
              These ty chk -> runCheck chk ty
              This _ty -> throwError $ TypeError "The constructor 'what-am-i' is missing a case"
              That _chk -> throwError $ TypeError $ "The constructor 'what-am-i' is not of type '" <> show tyName <> "'"
        cases' <- Map.toList <$> alignWithM alignCases eliminators checks
        pure $ SCase scrut' cases'
    -- (ty | isSubtypeOf _ ty, tm) -> error "TODO: How do I perform a subtyping check here?"
    (ty, _) -> throwError $ TypeError $ "'" <> "what-am-i" <> "' cannot be a subtype of '" <> show ty <> "'"

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
  SCnstr nm bndrs -> doConstructor nm bndrs
  SCase scrut patterns -> doCase scrut patterns
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

doConstructor :: Name -> [Syntax] -> EvalM Value
doConstructor nm args = do
  args' <- traverse eval args
  pure $ VCnstr nm args'

doCase :: Syntax -> [(Name, Syntax)] -> EvalM Value
doCase (SCnstr nm args) patterns =
  case find ((== nm) . fst) patterns of
    Just (_, body) -> eval $ foldl SAp body args
    Nothing -> error "impossible case in doCase"
doCase _ _ = error "impossible case in doCase"

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
quote l _ (VNeutral _ neu) = quoteNeutral l neu
quote _ _ VUnit = pure SUnit
quote _ _ VTru = pure STru
quote _ _ VFls = pure SFls
quote l ty (VRecord fields) = SRecord <$> traverse (traverse (quote l ty)) fields
quote _ _ (VNatural n) = pure $ SNatural n
quote _ _ (VInteger z) = pure $ SInteger z
quote _ _ (VReal r) = pure $ SReal r
quote l ty (VCnstr nm args) = SCnstr nm <$> traverse (quote l ty) args
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
  VIf ty t1 t2 -> liftA2 (SIf tm) (quote l ty t1) (quote l ty t2)
  -- NOTE: This never get constructed. Do I need them in STLC?
  VGet name -> pure $ SGet name tm
  VCase mot cases -> (SCase tm <$> traverse (traverse (quote l mot)) cases)

bindVar :: Type -> Lvl -> (Value -> Lvl -> a) -> a
bindVar ty lvl f =
  let v = VNeutral ty $ Neutral (VVar lvl) Nil
   in f v $ incLevel lvl

--------------------------------------------------------------------------------
-- Main

run :: Term -> Either (Error, Holes) (Syntax, Holes)
run term =
  case runTypecheckM (runSynth $ synth term) initEnv of
    (Left err, holes) -> Left (err, holes)
    (Right (type', syntax), holes) -> do
      let result = flip runEvalM Nil $ do
            value <- eval syntax
            quote initLevel type' value
      pure (result, holes)

main :: IO ()
main =
  -- \x. (\y. y) x
  case run (Anno (AdtTy "ListBool" `FuncTy` AdtTy "ListBool") (Cnstr "Cons" [Tru])) of
    Left err -> print err
    Right result -> print result

caseMatch :: Term
caseMatch =
  Anno
    BoolTy
    (Case (Anno (AdtTy "ListBool") (Cnstr "Cons" [Tru, Cnstr "Nil" []])) [("Nil", [], Fls), ("Cons", ["x", "xs"], Var "x")])

subTypeApT :: Term
subTypeApT =
  Ap
    ( Anno
        (RecordTy [("foo", BoolTy)] `FuncTy` BoolTy)
        (Lam "x" (Get "foo" (Var "x")))
    )
    recordT

recordT :: Term
recordT = Record [("foo", Tru), ("bar", Unit), ("baz", Unit)]

-- λp. if p then False else True
notT :: Term
notT =
  Anno
    (BoolTy `FuncTy` BoolTy)
    (Lam "x" (If (Var "x") Fls Tru))

-- λx. x
idenT :: Term
idenT =
  Anno
    (UnitTy `FuncTy` UnitTy)
    (Lam "x" Hole)

-- λf. f
idenT' :: Term
idenT' =
  Anno
    ((UnitTy `FuncTy` UnitTy) `FuncTy` (UnitTy `FuncTy` UnitTy))
    (Lam "f" (Var "f"))

-- λx. λy. x
constT :: Term
constT =
  Anno
    (UnitTy `FuncTy` (UnitTy `FuncTy` UnitTy))
    (Lam "x" (Lam (Name "_") (Var "x")))

-- λf. λx. f x
applyT :: Term
applyT =
  Anno
    ((UnitTy `FuncTy` UnitTy) `FuncTy` (UnitTy `FuncTy` UnitTy))
    (Lam "f" (Lam "x" (Ap (Var "f") (Var "x"))))

{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Main where

--------------------------------------------------------------------------------

import Control.Applicative (liftA2)
import Control.Monad.Except (MonadError (..))
import Control.Monad.Identity
import Control.Monad.Reader (MonadReader (..), asks)
import Control.Monad.Trans.Except (ExceptT (..))
import Control.Monad.Trans.Reader (Reader, ReaderT (..))
import Control.Monad.Trans.Writer.Strict (WriterT (..))
import Control.Monad.Writer.Strict (MonadWriter (..))
import Data.Align (Semialign (..))
import Data.Foldable (find)
import Data.Functor ((<&>))
import Data.Map (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.String
import Data.These

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
  | Zero
  | Succ Term
  | NatRec Term Term Term
  | Record [(Name, Term)]
  | Get Name Term
  | Cnstr Name [Term]
  | Case Term [(Name, [Name], Term)]
  | Anno Type Term
  | Hole
  deriving stock (Show, Eq, Ord)

data Type
  = FuncTy Type Type
  | PairTy Type Type
  | UnitTy
  | BoolTy
  | NatTy
  | RecordTy [(Name, Type)]
  | AdtTy Name
  deriving stock (Show, Eq, Ord)

data ArgSpec
  = Term Type
  | Rec [Type]
  deriving stock (Show, Eq, Ord)

data ConstrSpec
  = Constr Name [ArgSpec]
  deriving stock (Show, Eq, Ord)

data DataSpec
  = -- If we had type variables then this would be:
    -- Data Name [Name] [ConstrSpec]
    -- If we had Kinds then this would be:
    -- Data Name [Kind] [ConstrSpec]
    -- If we had MLTT then this would be:
    -- Data Name [Term] [ConstrSpec]
    Data Name [ConstrSpec]
  deriving stock (Show, Eq, Ord)

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
  | SZero
  | SSucc Syntax
  | SNatRec Syntax Syntax Syntax
  | SRecord [(Name, Syntax)]
  | SGet Name Syntax
  | SCnstr Name [Syntax]
  | SCase Syntax [(Name, [Name], Syntax)]
  | SHole Type
  deriving stock (Show, Eq, Ord)

data Value
  = VNeutral Type Neutral
  | VLam Name Closure
  | VPair Value Value
  | VUnit
  | VTru
  | VFls
  | VZero
  | VSucc Value
  | VRecord [(Name, Value)]
  | VCnstr Name [Value]
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

data Head
  = VVar Lvl
  | VHole Type
  deriving (Show, Eq, Ord)

data Frame
  = VApp Type Value
  | VFst
  | VSnd
  | VIf Type Value Value
  | VNatRec Type Value Value
  | VGet Name
  | VCase [(Name, Value)]
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
    adts :: Map Name DataSpec
  }
  deriving stock (Show, Eq, Ord)

stockADTs :: Map Name DataSpec
stockADTs =
  Map.fromList
    [ ("MaybeBool", Data "MaybeBool" [Constr "Nothing" [], Constr "Just" [Term BoolTy]]),
      ("ListBool", Data "ListBool" [Constr "Nil" [], Constr "Just" [Term BoolTy, Rec []]])
    ]

initEnv :: Env
initEnv = Env Nil [] 0 mempty stockADTs

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
      adts = adts
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
  deriving stock (Show)

newtype Holes = Holes {getHoles :: [Type]}
  deriving newtype (Show, Semigroup, Monoid)

newtype TypecheckM a = TypecheckM {runTypecheckM :: Env -> (Either Error a, Holes)}
  deriving
    (Functor, Applicative, Monad, MonadReader Env, MonadError Error, MonadWriter Holes)
    via (ExceptT Error (WriterT Holes (Reader Env)))

synth :: Term -> TypecheckM (Type, Syntax)
synth = \case
  Var bndr -> varTactic bndr
  Ap tm1 tm2 -> apTactic tm1 tm2
  Fst tm -> fstTactic tm
  Snd tm -> sndTactic tm
  Unit -> pure (UnitTy, SUnit)
  Tru -> pure (BoolTy, STru)
  Fls -> pure (BoolTy, SFls)
  If p tm1 tm2 -> ifTactic p tm1 tm2
  Zero -> pure (NatTy, SZero)
  Succ tm -> succTactic tm
  NatRec tm1 tm2 n -> natRecTactic tm1 tm2 n
  Record fields -> recordTactic fields
  Get name tm -> getTactic name tm
  Case tm patterns -> caseTactic tm patterns
  Hole -> throwError $ TypeError "Cannot synthesize a type hole"
  Anno ty tm -> (ty,) <$> check ty tm
  tm -> throwError $ TypeError $ "Cannot synthesize type for " <> show tm

check :: Type -> Term -> TypecheckM Syntax
check (FuncTy ty1 ty2) (Lam bndr tm) = lamTactic ty1 ty2 bndr tm
check ty Hole = holeTactic ty
check ty (Pair tm1 tm2) = pairTactic ty tm1 tm2
check ty (Cnstr nm bndrs) = constructorTactic ty nm bndrs
check ty tm =
  synth tm >>= \case
    (ty2, tm) | ty2 `subsumes` ty -> pure tm
    (ty2, _) -> throwError $ TypeError $ "Expected: " <> show ty <> ", but got: " <> show ty2

-- | Var Tactic
varTactic :: Name -> TypecheckM (Type, Syntax)
varTactic bndr = do
  ctx <- ask
  case resolveCell ctx bndr of
    Just Cell {..} -> do
      let quoted = flip runEvalM (locals ctx) $ quote (Lvl $ size ctx) cellType cellValue
      pure (cellType, quoted)
    Nothing -> throwError $ OutOfScopeError bndr

-- | Lambda Introduction Tactic
lamTactic :: Type -> Type -> Name -> Term -> TypecheckM Syntax
lamTactic ty1 ty2 bndr body = do
  ctx <- ask
  let var = freshCell ctx bndr ty1
  fiber <- local (bindCell var) $ check ty2 body
  pure $ SLam bndr fiber

-- | Lambda Elimination Tactic
apTactic :: Term -> Term -> TypecheckM (Type, Syntax)
apTactic tm1 tm2 =
  synth tm1 >>= \case
    (FuncTy ty1 ty2, f) -> do
      arg <- check ty1 tm2
      pure (ty2, SAp f arg)
    ty -> throwError $ TypeError $ "Expected a function type but got " <> show ty

-- | Pair Introduction Tactic
pairTactic :: Type -> Term -> Term -> TypecheckM Syntax
pairTactic (PairTy ty1 ty2) tm1 tm2 = do
  tm1' <- check ty1 tm1
  tm2' <- check ty2 tm2
  pure (SPair tm1' tm2')
pairTactic ty _ _ = throwError $ TypeError $ "Expected a Pair type but got " <> show ty

-- | Pair Fst Elimination Tactic
fstTactic :: Term -> TypecheckM (Type, Syntax)
fstTactic tm =
  synth tm >>= \case
    (PairTy ty1 _ty2, SPair tm1 _tm2) -> pure (ty1, tm1)
    (ty, _) -> throwError $ TypeError $ "Expected a Pair but got " <> show ty

-- | Pair Snd Elimination Tactic
sndTactic :: Term -> TypecheckM (Type, Syntax)
sndTactic tm =
  synth tm >>= \case
    (PairTy _ty1 ty2, SPair _tm1 tm2) -> pure (ty2, tm2)
    (ty, _) -> throwError $ TypeError $ "Expected a Pair but got " <> show ty

-- | Bool Elimination Tactic
ifTactic :: Term -> Term -> Term -> TypecheckM (Type, Syntax)
ifTactic p t1 t2 = do
  p' <- check BoolTy p
  (ty, t1') <- synth t1
  t2' <- check ty t2
  pure (ty, SIf p' t1' t2')

-- | Nat Successor Introduction Tactic
succTactic :: Term -> TypecheckM (Type, Syntax)
succTactic tm = do
  tm' <- check NatTy tm
  pure (NatTy, SSucc tm')

-- | Nat Elimination Tactic
natRecTactic :: Term -> Term -> Term -> TypecheckM (Type, Syntax)
natRecTactic tm1 tm2 n = do
  n' <- check NatTy n
  (zTy, tm1') <- synth tm1
  tm2' <- check (NatTy `FuncTy` (zTy `FuncTy` zTy)) tm2
  pure (zTy, SNatRec tm1' tm2' n')

-- | Record Introduction Tactic
recordTactic :: [(Name, Term)] -> TypecheckM (Type, Syntax)
recordTactic fields = do
  fields' <- traverse (traverse synth) fields
  let ty = fmap (fmap fst) fields'
      tm = fmap (fmap snd) fields'
  pure (RecordTy ty, SRecord tm)

-- | Record Elimination Tactic
getTactic :: Name -> Term -> TypecheckM (Type, Syntax)
getTactic name tm = do
  synth tm >>= \case
    (RecordTy fields, tm') ->
      case lookup name fields of
        Just ty -> pure (ty, SGet name tm')
        Nothing -> throwError $ TypeError $ "Record does not contain a field called " <> show name
    (ty, _) -> throwError $ TypeError $ "Expected a record type but got " <> show ty

-- | ADT Introduction Tactic
constructorTactic :: Type -> Name -> [Term] -> TypecheckM Syntax
constructorTactic (AdtTy tyName) nm bndrs = do
  asks (Map.lookup tyName . adts) >>= \case
    Just (Data _ cnstrs) ->
      case find (\(Constr nm' _) -> nm' == nm) cnstrs of
        Just (Constr _ args) | length args == length bndrs -> do
          params <- zipWithM check (fmap (\case Term ty -> ty; Rec _ -> (AdtTy tyName)) args) bndrs
          pure $ SCnstr nm params
        _ -> throwError $ TypeError $ "Data Constructor does not match type: " <> show tyName
    Nothing -> throwError $ OutOfScopeError nm
constructorTactic ty _ _ = throwError $ TypeError $ "Expected a type constructor but got " <> show ty

-- | ADT Elimination Tactic
--
-- The core idea is that given an ADT:
--
-- data ListBool = Nil | Cons Bool ListBool
--
-- We want to build an eliminator function:
--
-- bool-elim : (() -> A) -> (Bool -> A -> A) -> ListBool -> A
--
-- The 'DataSpec' for ListBool is:
--
-- Data "ListBool" [Constr "Nil" [], Constr "Just" [Term BoolTy, Rec []]]
--
-- From this we derive the recursion principle for our eliminator. The
-- elminator receives function per Data Constructor which returns our
-- goal type 'A'. The parameters on the constructor become parameters
-- on the function where recursive references are replaced by the goal
-- type:
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
caseTactic :: Term -> [(Name, [Name], Term)] -> TypecheckM (Type, Syntax)
caseTactic scrut patterns =
  -- 0. Check that the scrutinee is an ADT
  synth scrut >>= \case
    (AdtTy tyName, SCnstr nm args) -> do
      -- 1. Lookup the full ADT spec in the environment
      asks (Map.lookup tyName . asks adts) >>= \case
        Just (Data _ cnstrSpecs) -> do
          -- 2. Check that all ADT constructors are matched with a pattern and that the patterns have the correct number of binders.
          -- NOTE: Currently catch-all binder not supported.
          let patternMap = Map.fromList $ fmap (\(x, y, z) -> (x, (y, z))) patterns
              specMap = Map.fromList $ fmap (\(Constr nm args) -> (nm, args)) cnstrSpecs

          checkedPatterns <- alignWithM (checkPattern tyName) patternMap specMap
          -- 3. Check that all body terms are the same type.
          types <- forM patterns $ \(_, _, tm) -> do
            (ty, _) <- synth tm
            pure ty
          unless (all (== Prelude.head types) types) $ throwError $ TypeError "Case statement return types don't match"
          -- 4. Find the pattern which matches the scrutinee
          case Map.lookup nm checkedPatterns of
            -- 5. Check that the scrut args match the pattern
            Just (bndrs, tm) | length bndrs == length args -> do
              -- 6. check the body with the context extended to include all the binders
              ctx <- ask
              let vars = bndrs <&> uncurry (freshCell ctx)
              fiber <- local (bindCells vars) $ check (Prelude.head types) tm
              pure (Prelude.head types, fiber)
            _ -> throwError $ TypeError "Pattern does not contain the correct number of binders for scrutinee"
        Nothing -> throwError $ TypeError "Data constructor does not match any ADTs"
    (ty, _) -> throwError $ TypeError $ "Expected a type constructor but got " <> show ty

checkPattern :: Name -> These ([Name], Term) [ArgSpec] -> TypecheckM ([(Name, Type)], Term)
checkPattern tyName (These (binders, tm) argsSpec) = do
  unless (length binders == length argsSpec) $ throwError $ TypeError "binders didn't match constructor params"
  let argTypes = fmap (\case Term ty -> ty; Rec _ -> (AdtTy tyName)) argsSpec
  pure (zip binders argTypes, tm)
checkPattern _ _ = throwError $ TypeError "pattern doesn't match constructor"

-- | Type Hole Tactic
holeTactic :: Type -> TypecheckM Syntax
holeTactic ty = do
  tell (Holes [ty])
  pure (SHole ty)

--------------------------------------------------------------------------------
-- Subsumption

-- | ty1 <: ty2
subsumes :: Type -> Type -> Bool
subsumes (RecordTy fields1) (RecordTy fields2) =
  let fields1' = Map.fromList fields1
      fields2' = Map.fromList fields2
   in Map.isSubmapOfBy subsumes fields2' fields1'
subsumes super sub = super == sub

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
  SZero -> pure VZero
  SSucc tm -> VSucc <$> eval tm
  SNatRec tm1 tm2 n -> do
    n' <- eval n
    tm1' <- eval tm1
    tm2' <- eval tm2
    doNatRec n' tm1' tm2'
  SRecord fields -> doRecord fields
  SGet name tm -> eval tm >>= doGet name
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

doNatRec :: Value -> Value -> Value -> EvalM Value
doNatRec VZero z _f = pure z
doNatRec (VSucc n) z f = do
  hd <- doApply f n
  tl <- doNatRec n z f
  doApply hd tl
doNatRec (VNeutral ty neu) z f = do
  pure $ VNeutral ty $ pushFrame neu $ VNatRec ty z f
doNatRec _ _ _ = error "impossible case in doNatRec"

doRecord :: [(Name, Syntax)] -> EvalM Value
doRecord fields = VRecord <$> traverse (traverse eval) fields

doGet :: Name -> Value -> EvalM Value
doGet name (VRecord fields) =
  case lookup name fields of
    Nothing -> error "impossible case in doGet lookup"
    Just field -> pure field
doGet _ s = error $ show s -- "impossible case in doGet"

doConstructor :: Name -> [Syntax] -> EvalM Value
doConstructor nm args = do
  args' <- traverse eval args
  pure $ VCnstr nm args'

doCase :: Syntax -> [(Name, [Name], Syntax)] -> EvalM Value
doCase (SCnstr nm args) patterns = do
  args' <- traverse eval args
  case find (\(nm', _, _) ->  nm == nm') patterns of
    Just (_, bndrs, body) -> _
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
quote _ _ VZero = pure SZero
quote l ty (VSucc tm) = SSucc <$> quote l ty tm
quote l ty (VRecord fields) = SRecord <$> traverse (traverse (quote l ty)) fields
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
  VNatRec ty tm1 tm2 -> liftA2 (SNatRec tm) (quote l ty tm1) (quote l (NatTy `FuncTy` (ty `FuncTy` ty)) tm2)
  VGet name -> pure $ SGet name tm

bindVar :: Type -> Lvl -> (Value -> Lvl -> a) -> a
bindVar ty lvl f =
  let v = VNeutral ty $ Neutral (VVar lvl) Nil
   in f v $ incLevel lvl

--------------------------------------------------------------------------------
-- Main

run :: Term -> Either (Error, Holes) (Syntax, Holes)
run term =
  case runTypecheckM (synth term) initEnv of
    (Left err, holes) -> Left (err, holes)
    (Right (type', syntax), holes) -> do
      let result = flip runEvalM Nil $ do
            value <- eval syntax
            -- error $ show type' <> "\n" <> show value
            quote initLevel type' value
      pure (result, holes)

main :: IO ()
main =
  case run subTypeApT of
    Left err -> print err
    Right result -> print result

subTypeApT :: Term
subTypeApT =
  Ap
    ( Anno
        (RecordTy [("foo", BoolTy)] `FuncTy` BoolTy)
        (Lam "x" (Get "foo" (Var "x")))
    )
    recordT

recordT :: Term
recordT = Record [("foo", Tru), ("bar", Zero), ("baz", Unit)]

addT :: Term
addT =
  Anno
    (NatTy `FuncTy` (NatTy `FuncTy` NatTy))
    (Lam "n" (Lam "m" (NatRec (Var "m") (Lam "x" (Lam "y" (Succ (Var "y")))) (Var "n"))))

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

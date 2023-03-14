{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Main where

--------------------------------------------------------------------------------

import Data.Foldable (find, sequenceA_)
import Data.Maybe (fromMaybe)
import Data.String

--------------------------------------------------------------------------------
-- Utils

data SnocList a
  = Snoc (SnocList a) a
  | Nil
  deriving (Show, Eq, Ord, Functor, Foldable)

zipSnocWith :: (a -> b -> c) -> SnocList a -> SnocList b -> SnocList c
zipSnocWith f = go
  where
    go Nil _ = Nil
    go _ Nil = Nil
    go (Snoc as a) (Snoc bs b) = Snoc (go as bs) (f a b)

zipSnocWithM_ :: (Applicative m) => (a -> b -> m c) -> SnocList a -> SnocList b -> m ()
zipSnocWithM_ f xs ys = sequenceA_ (zipSnocWith f xs ys)

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
  = Var Name
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

data Syntax
  = SVar Ix
  | SLam Name Syntax
  | SAp Syntax Syntax
  | SPair Syntax Syntax
  | SFst Syntax
  | SSnd Syntax
  | SUnit
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
    size :: Int
  }
  deriving stock (Show, Eq, Ord)

initEnv :: Env
initEnv = Env Nil [] 0

extendLocalNames :: Env -> Cell -> Env
extendLocalNames e@Env {localNames} cell = e {localNames = cell : localNames}

bindCell :: Env -> Cell -> Env
bindCell Env {..} cell@Cell {..} =
  Env
    { locals = Snoc locals cellValue,
      localNames = cell : localNames,
      size = size + 1
    }

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

synth :: Env -> Term -> Either Error (Type, Syntax)
synth ctx = \case
  Var bndr -> varTactic ctx bndr
  Ap tm1 tm2 -> apTactic ctx tm1 tm2
  Anno ty tm -> (ty,) <$> check ctx ty tm
  Unit -> pure (UnitTy, SUnit)
  tm -> Left $ TypeError $ "Cannot synthesize type for " <> show tm

check :: Env -> Type -> Term -> Either Error Syntax
check ctx (FuncTy ty1 ty2) (Lam bndr tm) = lamTactic ctx ty1 ty2 bndr tm
check ctx ty tm =
  case synth ctx tm of
    Right (ty2, tm) | ty == ty2 -> pure tm
    Right ty2 -> Left $ TypeError $ "Expected: " <> show ty <> ", but got: " <> show ty2
    Left err -> Left err

varTactic :: Env -> Name -> Either Error (Type, Syntax)
varTactic ctx bndr =
  case resolveCell ctx bndr of
    Just Cell {..} -> pure (cellType, quote (Lvl $ size ctx) cellType cellValue)
    Nothing -> Left $ OutOfScopeError bndr

lamTactic :: Env -> Type -> Type -> Name -> Term -> Either Error Syntax
lamTactic ctx ty1 ty2 bndr body = do
  let var = freshCell ctx bndr ty1
  fiber <- check (bindCell ctx var) ty2 body
  pure $ SLam bndr fiber

apTactic :: Env -> Term -> Term -> Either Error (Type, Syntax)
apTactic ctx tm1 tm2 =
  synth ctx tm1 >>= \case
    (FuncTy ty1 ty2, f) -> do
      arg <- check ctx ty1 tm2
      pure (ty2, SAp f arg)
    ty -> Left $ TypeError $ "Expected a function type but got " <> show ty

--------------------------------------------------------------------------------
-- Evaluator

eval :: SnocList Value -> Syntax -> Value
eval env = \case
  SVar (Ix ix) -> fromMaybe (error "internal error") $ nth env ix
  SLam bndr body -> VLam bndr (Closure env body)
  SAp tm1 tm2 ->
    let fun = eval env tm1
        arg = eval env tm2
     in doApply fun arg
  SPair tm1 tm2 ->
    let tm1' = eval env tm1
        tm2' = eval env tm2
     in VPair tm1' tm2'
  SFst tm -> doFst $ eval env tm
  SSnd tm -> doSnd $ eval env tm
  SUnit -> VUnit

doApply :: Value -> Value -> Value
doApply (VLam _ clo) arg = instantiateClosure clo arg
doApply (VNeutral (FuncTy ty1 ty2) neu) arg = VNeutral ty2 (pushFrame neu (VApp ty1 arg))
doApply _ _ = error "impossible case in doApply"

doFst :: Value -> Value
doFst (VPair a _b) = a
doFst _ = error "impossible case in doFst"

doSnd :: Value -> Value
doSnd (VPair _a b) = b
doSnd _ = error "impossible case in doSnd"

instantiateClosure :: Closure -> Value -> Value
instantiateClosure (Closure env body) v = eval (Snoc env v) body

--------------------------------------------------------------------------------
-- Quoting

quote :: Lvl -> Type -> Value -> Syntax
quote l (FuncTy ty1 ty2) (VLam bndr clo@(Closure _env _body)) =
  let body = bindVar ty1 l $ \v l' ->
        quote l' ty2 $ instantiateClosure clo v
   in SLam bndr body
quote l (FuncTy ty1 ty2) f =
  let body = bindVar ty1 l $ \v l' ->
        quote l' ty2 (doApply f v)
   in SLam "_" body
quote l (PairTy ty1 ty2) (VPair tm1 tm2) =
  let tm1' = quote l ty1 tm1
      tm2' = quote l ty2 tm2
   in SPair tm1' tm2'
quote l _ (VNeutral _ neu) = quoteNeutral l neu
quote _ _ VUnit = SUnit
quote _ _ _ = error "impossible case in quote"

quoteLevel :: Lvl -> Lvl -> Ix
quoteLevel (Lvl l) (Lvl x) = Ix (l - (x + 1))

quoteNeutral :: Lvl -> Neutral -> Syntax
quoteNeutral l Neutral {..} = foldl (quoteFrame l) (quoteHead l head) spine

quoteHead :: Lvl -> Head -> Syntax
quoteHead l (VVar x) = SVar (quoteLevel l x)

quoteFrame :: Lvl -> Syntax -> Frame -> Syntax
quoteFrame l tm = \case
  VApp ty arg -> SAp tm (quote l ty arg)
  VFst -> SFst tm
  VSnd -> SSnd tm

bindVar :: Type -> Lvl -> (Value -> Lvl -> a) -> a
bindVar ty lvl f =
  let v = VNeutral ty $ Neutral (VVar lvl) Nil
   in f v $ incLevel lvl

--------------------------------------------------------------------------------
-- Main

main :: IO ()
main =
  let term' = Ap idenT Unit
   in case synth initEnv term' of
        Left err -> print err
        Right (type', tm') ->
          print $ quote (Lvl 0) type' $ eval Nil tm'

-- λx. x
idenT :: Term
idenT =
  Anno
    (UnitTy `FuncTy` UnitTy)
    (Lam (Name "x") (Var "x"))

-- λf. f
idenT' :: Term
idenT' =
  Anno
    ((UnitTy `FuncTy` UnitTy) `FuncTy` (UnitTy `FuncTy` UnitTy))
    (Lam (Name "f") (Var "f"))

-- λx. λy. x
constT :: Term
constT =
  Anno
    (UnitTy `FuncTy` (UnitTy `FuncTy` UnitTy))
    (Lam (Name "x") (Lam (Name "_") (Var "f")))

-- λf. λx. f x
applyT :: Term
applyT =
  Anno
    ((UnitTy `FuncTy` UnitTy) `FuncTy` (UnitTy `FuncTy` UnitTy))
    (Lam (Name "f") (Lam (Name "x") (Ap (Var "f") (Var "x"))))

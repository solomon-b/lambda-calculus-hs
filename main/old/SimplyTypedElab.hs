{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TupleSections #-}

module Main where

--------------------------------------------------------------------------------

import Control.Monad.State
import Data.Foldable (find)
import Data.Functor (($>))
import Data.List ((\\))
import Data.Map (Map)
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe)
import Debug.Trace
import GHC.Conc (labelThread)

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
            (Snoc xs _, i) -> go (xs, i - 1)
       in go (xs, i)

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

bindVar :: Env -> Cell -> Env
bindVar Env {..} cell@Cell {..} =
  Env
    { locals = Snoc locals cellValue,
      localNames = cell : localNames,
      size = size + 1
    }

--------------------------------------------------------------------------------
-- Terms

data Type = Type :-> Type | UnitT | BoolT
  deriving stock (Show, Eq, Ord)

-- NOTE: 'ConcreteSyntax' would also contain spans if we were parsing.
data ConcreteSyntax
  = CSVar Name
  | CSAbs Name ConcreteSyntax
  | CSApp ConcreteSyntax [ConcreteSyntax]
  | CSUnit
  | CSTrue
  | CSFalse
  | CSIf ConcreteSyntax ConcreteSyntax ConcreteSyntax
  | CSAnno ConcreteSyntax Type
  | CSHole
  deriving stock (Show, Eq, Ord)

data Syntax
  = SVar Ix
  | SAbs Name Syntax
  | SApp Syntax Syntax
  | SUnit
  | STrue
  | SFalse
  | SIf Syntax Syntax Syntax
  | SHole Type Int
  deriving stock (Show, Eq, Ord)

data Value
  = VNeutral Type Neutral
  | VLam Name Closure
  | VTrue
  | VFalse
  | VUnit
  deriving stock (Show, Eq, Ord)

data Neutral = Neutral {head :: Head, spine :: SnocList Frame}
  deriving stock (Show, Eq, Ord)

data Head
  = VVar Lvl
  | VHole Type Int
  deriving (Show, Eq, Ord)

data Frame = VApp {ty :: Type, arg :: Value}
  deriving stock (Show, Eq, Ord)

pushFrame :: Neutral -> Frame -> Neutral
pushFrame Neutral {..} frame = Neutral {head = head, spine = Snoc spine frame}

data Closure = Closure {env :: EvalEnv, body :: Syntax}
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
  deriving newtype (Show, Eq, Ord)

data Error
  = NotFound
  | TypeError String
  | TypeHole Type
  | HoleInSynth
  deriving (Show)

--------------------------------------------------------------------------------
-- Typechecking

resolveCell :: Env -> Name -> Maybe Cell
resolveCell Env {..} bndr = find ((== bndr) . cellName) localNames

synth :: Env -> ConcreteSyntax -> Either Error (Type, Syntax)
synth ctx = \case
  CSVar bndr ->
    case resolveCell ctx bndr of
      Just Cell {..} -> pure (cellType, quote (Lvl $ size ctx) cellType cellValue)
      Nothing -> Left NotFound
  CSApp f args -> do
    f' <- synth ctx f
    foldM (synAp ctx) f' args
  CSTrue -> pure (BoolT, STrue)
  CSFalse -> pure (BoolT, SFalse)
  CSUnit -> pure (UnitT, SUnit)
  CSIf t1 t2 t3 -> do
    check ctx t1 BoolT
    t2' <- synth ctx t2
    t3' <- synth ctx t3
    if fst t2' == fst t3'
      then pure t2'
      else Left $ TypeError $ "Type mismatch: " <> show (fst t2') <> " /= " <> show (fst t3')
  CSAnno t1 ty -> (ty,) <$> check ctx t1 ty
  CSHole -> Left HoleInSynth
  _ -> Left $ TypeError "cannot synthesize type."

synAp :: Env -> (Type, Syntax) -> ConcreteSyntax -> Either Error (Type, Syntax)
synAp ctx (tyA :-> tyB, f) arg = do
  arg' <- check ctx arg tyA
  pure (tyB, SApp f arg')
synAp _ ty _ = Left $ TypeError $ "Not a function type: " <> show ty

check :: Env -> ConcreteSyntax -> Type -> Either Error Syntax
check ctx a@(CSAbs bndr body) ty =
  case ty of
    tyA :-> tyB -> do
      let var = freshCell ctx bndr tyA
      fiber <- check (bindVar ctx var) body tyB
      pure $ SAbs bndr fiber
    ty' -> Left $ TypeError $ "Abs requires a function type, but got a: " <> show ty'
check ctx CSHole ty = do
  -- Note: For demonstration purposes here we simply return the first
  -- hole encountered. However, in a more complete system we would
  -- convert from a Concrete Syntax hole to a Syntax hole and have
  -- some effect to accumulate all the holes:

  -- label <- freshHole
  -- let hole = SHole ty label
  -- logHole hole
  -- pure hole

  -- This would allow us to continue typechecking and collect all the
  -- holes for reporting to the user. The required Hole constructors
  -- are included in our types to hint at this but the actual
  -- implementation is deferred so as to not obscure the core
  -- elaborator behavior.
  Left $ TypeHole ty
check ctx t1 ty = do
  (ty', t1') <- synth ctx t1
  if ty' == ty
    then pure t1'
    else Left $ TypeError $ "Expected type " <> show ty <> " but got " <> show ty'

freshVar :: Env -> Type -> Value
freshVar Env {size} ty = VNeutral ty $ Neutral (VVar $ Lvl size) Nil

freshCell :: Env -> Name -> Type -> Cell
freshCell ctx name ty = Cell name ty (freshVar ctx ty)

--------------------------------------------------------------------------------
-- Evaluation

newtype EvalEnv = EvalEnv (SnocList Value, Int)
  deriving stock (Show, Eq, Ord)

initEvalEnv :: EvalEnv
initEvalEnv = EvalEnv (Nil, 0)

extendEvalEnv :: EvalEnv -> Value -> EvalEnv
extendEvalEnv e@(EvalEnv (locals, size)) val = EvalEnv (Snoc locals val, size + 1)

eval :: EvalEnv -> Syntax -> Value
eval env@(EvalEnv (locals, size)) = \case
  SVar (Ix ix) -> fromMaybe (error "internal error") $ nth locals ix
  SAbs bndr body -> VLam bndr (Closure env body)
  SApp t1 t2 ->
    let fun = eval env t1
        arg = eval env t2
     in doApply fun arg
  STrue -> VTrue
  SFalse -> VFalse
  SUnit -> VUnit
  SIf t1 t2 t3 -> doIf (eval env t1) (eval env t2) (eval env t3)
  SHole ty ix -> VNeutral ty $ Neutral (VHole ty ix) Nil

doApply :: Value -> Value -> Value
doApply (VLam _ clo) arg =
  instantiateClosure clo arg
doApply (VNeutral (ty1 :-> ty2) neu) arg =
  VNeutral ty2 (pushFrame neu (VApp ty1 arg))
doApply t1 t2 = error "Internal error: impossible case in doApply"

instantiateClosure :: Closure -> Value -> Value
instantiateClosure (Closure env body) v = eval (extendEvalEnv env v) body

doIf :: Value -> Value -> Value -> Value
doIf VTrue t2 t3 = t2
doIf VFalse t2 t3 = t3

quote :: Lvl -> Type -> Value -> Syntax
quote _ UnitT _ = SUnit
quote _ BoolT VTrue = STrue
quote _ BoolT VFalse = SFalse
quote l ty@(tyA :-> tyB) v@(VLam bndr clo@(Closure env body)) =
  let xVal = VNeutral tyA $ Neutral (VVar l) Nil
   in SAbs bndr $ quote (incLevel l) tyB $ instantiateClosure clo xVal
quote l ty@(tyA :-> tyB) v =
  let xVal = VNeutral tyA $ Neutral (VVar l) Nil
   in SAbs (Name "_") $ quote (incLevel l) tyB $ doApply v xVal
quote l ty1 (VNeutral ty2 neu) =
  if ty1 == ty2
    then quoteNeutral l neu
    else error "Internal error while quoting"

quoteLevel :: Lvl -> Lvl -> Ix
quoteLevel env@(Lvl l) (Lvl x) = Ix (l - (x + 1))

quoteNeutral :: Lvl -> Neutral -> Syntax
quoteNeutral l Neutral {..} = foldl (quoteFrame l) (quoteHead l head) spine

quoteHead :: Lvl -> Head -> Syntax
quoteHead l = \case
  VVar x -> SVar (quoteLevel l x)
  VHole ty ix -> (SHole ty ix)

quoteFrame :: Lvl -> Syntax -> Frame -> Syntax
quoteFrame l t1 VApp {..} = SApp t1 (quote l ty arg)

normalize :: ConcreteSyntax -> Syntax
normalize term =
  case synth initEnv term of
    Right (ty, term') ->
      let val = eval initEvalEnv term'
       in quote (Lvl 0) ty val
    Left err -> error $ show err

--------------------------------------------------------------------------------
-- Prettyprinter

pp :: SnocList Name -> Syntax -> String
pp env = \case
  SVar (Ix ix) -> maybe ("![bad index " <> show ix <> "]!") getName $ nth env ix
  SAbs bndr body -> "λ " <> getName bndr <> " . " <> pp (Snoc env bndr) body
  SApp t1 t2 -> pp env t1 <> " " <> pp env t2
  STrue -> "True"
  SFalse -> "False"
  SUnit -> "Unit"
  SIf t1 t2 t3 -> "if " <> pp env t2 <> " then " <> pp env t2 <> " else " <> pp env t3
  SHole _ ix -> "_" <> show ix

--------------------------------------------------------------------------------
-- Main

-- λx. x
idenT :: ConcreteSyntax
idenT = CSAnno (CSAbs (Name "x") (CSVar (Name "x"))) (UnitT :-> UnitT)

-- λx. λy. x
constT :: ConcreteSyntax
constT = CSAnno (CSAbs (Name "x") (CSAbs (Name "_") (CSVar (Name "x")))) (BoolT :-> (UnitT :-> BoolT))

notT :: ConcreteSyntax
notT =
  CSAnno
    (CSAbs (Name "p") (CSIf (CSVar (Name "p")) CSTrue CSFalse))
    (BoolT :-> BoolT)

main :: IO ()
main = do
  -- let term = CSApp (CSApp constT [CSTrue]) [CSUnit]
  let term = CSAnno (CSAbs (Name "f") (CSVar (Name "f"))) ((BoolT :-> BoolT) :-> (BoolT :-> BoolT))
  case synth initEnv term of
    Left err -> print err
    Right (ty, tm) -> do
      let val = eval initEvalEnv tm
      putStrLn $ "Type: " <> show ty
      putStrLn $ "Syntax: " <> show tm
      putStrLn $ "Syntax Pretty: " <> pp Nil tm
      putStrLn $ "Value: " <> show val
      putStrLn $ "Quoted: " <> show (quote (Lvl 0) ty val)
      putStrLn $ "Quoted Pretty: " <> pp Nil (quote (Lvl 0) ty val)

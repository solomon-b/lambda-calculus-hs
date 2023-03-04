{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}

module Main where

--------------------------------------------------------------------------------

import Control.Monad.State
import Data.Functor (($>))
import Data.List ((\\))
import Data.Map (Map)
import qualified Data.Map.Strict as M

--------------------------------------------------------------------------------
-- Terms

data Term
  = Var Name
  | Abs Name Term
  | App Term Term
  | Unit
  | T
  | F
  | If Term Term Term
  | Anno Term Type
  deriving (Show)

data Type = Type :-> Type | UnitT | BoolT
  deriving (Show, Eq)

type Gamma = Env Type

initCtx :: Gamma
initCtx = initEnv

data Value
  = VTrue
  | VFalse
  | VUnit
  | VClosure (Env Value) Name Term
  | VNeutral Type Neutral
  deriving (Show)

data Neutral
  = NVar Name
  | NApp Neutral Normal
  | NIff Neutral Normal Normal
  deriving (Show)

data Normal = Normal {normalType :: Type, normalValue :: Value}
  deriving (Show)

data Name = Name String Int
  deriving stock (Show, Eq, Ord)

newtype Env val = Env [val]
  deriving stock (Show, Functor)

initEnv :: Env val
initEnv = Env []

data Error = NotFound Name | TypeError String
  deriving (Show)

lookupVar :: Env val -> Name -> Either Error val
lookupVar (Env env) n@(Name bndr i) = maybe (Left $ NotFound n) Right $ env !? i

(!?) :: [a] -> Int -> Maybe a
xs !? n
  | n < 0 = Nothing
  | otherwise =
      foldr
        ( \x r k -> case k of
            0 -> Just x
            _ -> r (k - 1)
        )
        (const Nothing)
        xs
        n

extend :: Env val -> val -> Env val
extend (Env env) val = Env (val : env)

--------------------------------------------------------------------------------
-- Debrujin Indices

shift :: Int -> Int -> Term -> Term
shift d c = \case
  Var (Name bndr k) | k < c -> Var (Name bndr k)
  Var (Name bndr k) -> Var (Name bndr (k + d))
  Abs bndr t1 -> Abs bndr (shift d (c + 1) t1)
  App t1 t2 -> App (shift d c t1) (shift d c t2)
  If t1 t2 t3 -> If (shift d c t1) (shift d c t2) (shift d c t3)
  Anno t1 ty -> Anno (shift d c t1) ty
  t -> t

subst :: Int -> Term -> Term -> Term
subst j s = \case
  Var (Name bndr k) | k == j -> s
  Abs bndr t1 -> Abs bndr (subst (j + 1) (shift 1 0 s) t1)
  App t1 t2 -> App (subst j s t1) (subst j t1 t2)
  If t1 t2 t3 -> If (subst j s t1) (subst j s t2) (subst j s t3)
  Anno t1 ty -> Anno (subst j s t1) ty
  t -> t

substTop :: Term -> Term -> Term
substTop s t = shift (-1) 0 (subst 0 (shift 1 0 s) t)

--------------------------------------------------------------------------------
-- Typechecking

synth :: Gamma -> Term -> Either Error Type
synth ctx = \case
  Var x -> lookupVar ctx x
  App t1 t2 ->
    synth ctx t1 >>= \case
      tyA :-> tyB -> do
        check ctx (substTop t1 t2) tyA
        pure tyB
      ty -> Left (TypeError $ "Not a function type: " ++ show ty)
  T -> pure BoolT
  F -> pure BoolT
  Unit -> pure UnitT
  If t1 t2 t3 -> do
    check ctx t1 BoolT
    ty2 <- synth ctx t2
    ty3 <- synth ctx t3
    if ty2 == ty3
      then pure ty2
      else Left $ TypeError $ "Type mismatch: " <> show ty2 <> " /= " <> show ty3
  Anno t1 ty -> check ctx t1 ty $> ty
  _ -> Left $ TypeError "cannot synthesize type."

check :: Gamma -> Term -> Type -> Either Error ()
check ctx (Abs bndr body) ty =
  case ty of
    tyA :-> tyB -> check (extend ctx tyA) body tyB
    ty' -> Left $ TypeError $ "Abs requires a function type, but got a: " <> show ty'
check ctx t1 ty = do
  ty' <- synth ctx t1
  if ty' == ty
    then pure ()
    else Left $ TypeError $ "Expected type " <> show ty <> " but got " <> show ty'

--------------------------------------------------------------------------------
-- Evaluation

eval :: Env Value -> Term -> Value
eval env = \case
  Var x -> either (error "internal error") id $ lookupVar env x
  Abs x body -> VClosure env x body
  App t1 t2 ->
    let fun = eval env t1
        arg = eval env t2
     in doApply fun arg
  T -> VTrue
  F -> VFalse
  Unit -> VUnit
  If t1 t2 t3 -> doIf (eval env t1) (eval env t2) (eval env t3)
  Anno t1 ty -> eval env t1

doApply :: Value -> Value -> Value
doApply (VClosure env x body) arg =
  eval (extend env arg) body
doApply (VNeutral (ty1 :-> ty2) neu) arg =
  VNeutral ty2 (NApp neu (Normal ty1 arg))

doIf :: Value -> Value -> Value -> Value
doIf VTrue t2 t3 = t2
doIf VFalse t2 t3 = t3

quote :: [Name] -> Type -> Value -> Term
quote used UnitT VUnit = Unit
quote used BoolT VTrue = T
quote used BoolT VFalse = F
quote used (tyA :-> tyB) fun@(VClosure _ x _) =
  let xVal = VNeutral tyA (NVar x)
   in Abs x (quote used tyB (doApply fun xVal))
quote used ty1 (VNeutral ty2 neu) =
  if ty1 == ty2
    then quoteNeutral used neu
    else error "Internal error while quoting"

quoteNormal :: [Name] -> Normal -> Term
quoteNormal used (Normal t v) = quote used t v

quoteNeutral :: [Name] -> Neutral -> Term
quoteNeutral used (NVar x) = Var x
quoteNeutral used (NApp f a) = App (quoteNeutral used f) (quoteNormal used a)
quoteNeutral used (NIff p a b) = If (quoteNeutral used p) (quoteNormal used a) (quoteNormal used b)

normalize :: Term -> Term
normalize term =
  case synth initEnv term of
    Right ty ->
      let val = eval initEnv term
       in quote [] ty val
    Left err -> error $ show err

--------------------------------------------------------------------------------
-- main

-- λx. x
idenT :: Term
idenT = Anno (Abs (Name "x" 0) (Var (Name "x" 0))) (UnitT :-> UnitT)

-- λx. λy. x
constT :: Term
constT = Anno (Abs (Name "x" 1) (Abs (Name "_" 0) (Var (Name "x" 1)))) (BoolT :-> (UnitT :-> BoolT))

notT :: Term
notT =
  Anno
    (Abs (Name "p" 0) (If (Var (Name "p" 0)) T F))
    (BoolT :-> BoolT)

main :: IO ()
main = do
  let term = App (App constT T) Unit
  print $ synth initCtx term
  print term
  print (normalize term)

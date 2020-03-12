{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
module Main where

import Data.Map (Map)
import qualified Data.Map.Strict as M
import Data.List ((\\))
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Control.Lens

-------------
--- Terms ---
-------------

data Term = Var String
          | Abs String Type Term
          | App Term Term
          | TAbs String Kind Term
          | TApp Term Type
          | Unit
          | T
          | F
          | If Term Term Term
  deriving Show

infixr 0 :->
data Type = Type :-> Type
          | TVar String
          | Forall String Kind Type
          | TyAbs String Kind Type
          | TyApp Type Type
          | UnitT
          | BoolT
  deriving (Show, Eq)

infixr 0 :=>
data Kind = Star | Kind :=> Kind
  deriving (Show, Eq)

data Gamma =
  Gamma { _context :: Map String Type
        , _contextT :: Map String Kind
        }
makeLenses ''Gamma

data TypeErr = TypeError | KindError deriving (Show, Eq)

----------------------
--- Pretty Printer ---
----------------------

class Show a => Pretty a where
  pretty :: a -> String
  pretty = show

instance Pretty Term where
  pretty = \case
    Var x -> x
    Abs bndr ty t0 -> "(λ" ++ bndr ++ " : " ++ pretty ty ++ " . " ++ pretty t0 ++ ")"
    App t1 t2 -> pretty t1 ++ " " ++ pretty t2
    TAbs bndr k t0 -> "(Λ" ++ bndr ++ " :: " ++ pretty k ++ " . " ++ pretty t0 ++ ")"
    TApp t0 ty -> pretty t0 ++ " " ++ "[" ++ pretty ty ++ "]"
    Unit -> "Unit"
    T -> "True"
    F -> "False"
    If t0 t1 t2 -> "If " ++ pretty t0 ++ " then " ++ pretty t1 ++ " else " ++ pretty t2

instance Pretty Type where
  pretty = \case
    TVar x -> x
    TyAbs b k ty -> "(" ++ b ++ " :: " ++ pretty k ++ " . " ++ pretty ty ++ ")"
    TyApp ty1 ty2 -> pretty ty1 ++ " " ++ pretty ty2
    ty0 :-> ty1 -> pretty ty0 ++ " -> " ++ pretty ty1
    Forall x k ty -> "∀" ++ x ++ " :: " ++ pretty k ++ " . " ++ pretty ty
    UnitT -> "Unit"
    BoolT -> "Bool"

instance Pretty Kind where
  pretty = \case
    Star -> "*"-- "★"
    k1 :=> k2 -> "(" ++ pretty k1 ++ " -> " ++ pretty k2 ++ ")"

------------------------
--- Alpha Conversion ---
------------------------

data Stream a = Stream a (Stream a)

data AlphaContext =
  AlphaContext { _names :: Stream String
               , _namesT :: Stream String
               , _register :: Map String String
               }
makeLenses ''AlphaContext

namesStream :: [String]
namesStream = (pure <$> ['a'..'z']) ++ (flip (:) <$> (show <$> [1..]) <*> ['a' .. 'z'])

typeNamesStream :: [String]
typeNamesStream = (pure <$> ['A'..'Z']) ++ (flip (:) <$> (show <$> [1..]) <*> ['A' .. 'Z'])

stream :: [String] -> Stream String
stream (x:xs) = Stream x (stream xs)

alphaT :: Type -> State AlphaContext Type
alphaT = \case
  TVar bndr ->
    use (register . at bndr) >>= \case
      Just bndr' -> pure $ TVar bndr'
      Nothing -> error "Something impossible happened"
  Forall bndr k ty -> do
    use (register . at bndr) >>= \case
      Just bndr' -> Forall bndr' k <$> alphaT ty
      Nothing -> do
        Stream fresh rest <- use namesT
        namesT .= rest
        register %= M.insert bndr fresh
        ty' <- alphaT ty
        pure $ Forall fresh k ty'
  ty1 :-> ty2 -> do
    ty1' <- alphaT ty1
    ty2' <- alphaT ty2
    pure $ ty1' :-> ty2'
  --TyAbs bndr k ty -> do
  --TyApp ty1 ty2 -> do
  --  ty1' <- alphaT ty1
  --  ty2' <- alphaT ty2
  --  pure $ TyApp ty1' ty2'
  t -> pure t

alpha :: Term -> State AlphaContext Term
alpha = \case
  Var x -> do
    mx <- gets (M.lookup x . _register)
    case mx of
      Just x' -> pure $ Var x'
      Nothing -> error "Something impossible happened"
  App t1 t2 -> do
    t1' <- alpha t1
    t2' <- alpha t2
    pure $ App t1' t2'
  Abs bndr ty term -> do
    (Stream fresh rest) <- gets _names
    names .= rest
    register %= M.insert bndr fresh
    term' <- alpha term
    pure $ Abs fresh ty term'
  TApp t tyBndr -> do
    t' <- alpha t
    tyBndr' <- alphaT tyBndr
    pure $ TApp t' tyBndr'
  TAbs tyBndr k term -> do
    Stream fresh' rest' <- use namesT
    regstry <- use register
    namesT .= rest'
    register %= M.insert tyBndr fresh'
    term' <- alpha term
    pure $ TAbs fresh' k term'
  If t1 t2 t3 -> do
    t1' <- alpha t1
    t2' <- alpha t2
    t3' <- alpha t3
    pure (If t1' t2' t3')
  t -> pure t

emptyAlphaContext :: AlphaContext
emptyAlphaContext = AlphaContext (stream namesStream) (stream typeNamesStream) M.empty

alphaconvert :: Term -> Term
alphaconvert term = evalState (alpha term) emptyAlphaContext

--------------------
--- Kindchecking ---
--------------------

kindcheck :: Type -> TypecheckM Kind
kindcheck (TVar bndr) = do
    k1 <- view (contextT . at bndr)
    maybe (error $ "Missing bndr " ++ bndr ++ ": " ++ show k1) pure k1
kindcheck (TyAbs bndr k1 ty) = do
  k2 <- local (contextT %~ M.insert bndr k1) (kindcheck ty)
  pure $ k1 :=> k2
kindcheck (TyApp ty1 ty2) =
  kindcheck ty1 >>= \case
    k11 :=> k12 ->
      kindcheck ty2 >>= \k2 ->
        if k2 == k11 then pure k12 else throwError KindError
    _ -> throwError KindError
kindcheck (ty1 :-> ty2) = do
  k1 <- kindcheck ty1
  k2 <- kindcheck ty2
  if (k1, k2) == (Star, Star) then pure Star else throwError KindError
kindcheck ty = pure Star

------------------------
--- Type Equivalence ---
------------------------

tyeq :: Type -> Type -> Bool
tyeq (s1 :-> s2) (t1 :-> t2) = tyeq s1 t1 && tyeq s2 t2
tyeq (TyAbs b1 k1 s2) (TyAbs b2 k2 t2) = k1 == k2 && tyeq s2 t2
tyeq (TyApp (TyAbs b1 k11 s12) s2) t1 =
  tyeq (substT b1 s2 s12) t1
tyeq s1 (TyApp (TyAbs b2 k11 t12) t2) =
  tyeq s1 (substT b2 t2 t12)
tyeq (TyApp s1 s2) (TyApp t1 t2) = s1 == t1 && s2 == t2
tyeq (Forall b1 k1 ty1) (Forall b2 k2 ty2) = k1 == k2 && tyeq ty1 ty2
tyeq s1 t1 = s1 == t1

unify :: [(String, String)] -> Type -> Type -> Bool
unify names (TVar a) (TVar b) =
  if a `elem` (fmap fst names) || b `elem` (fmap snd names)
    then (a, b) `elem` names
    else tyeq (TVar a) (TVar b)
unify names (TyAbs b1 k1 tyA) (TyAbs b2 k2 tyB) = unify ((b1, b2):names) tyA tyB
unify names (TyApp s1 s2) (TyApp t1 t2) = unify names s1 t1 && unify names s2 t2
unify names (tyA :-> tyB) (tyA' :-> tyB') = unify names tyA tyA' && unify names tyB tyB'
unify names tyA tyB = tyeq tyA tyB

--------------------
--- Typechecking ---
--------------------

newtype TypecheckM a =
  TypecheckM { unTypecheckM :: ExceptT TypeErr (Reader Gamma) a }
  deriving (Functor, Applicative, Monad, MonadReader Gamma, MonadError TypeErr)

emptyGamma :: Gamma
emptyGamma = Gamma mempty mempty

runTypecheckM :: TypecheckM a -> Either TypeErr a
runTypecheckM = flip runReader emptyGamma . runExceptT . unTypecheckM

typecheck :: Term -> TypecheckM Type
typecheck = \case
  Var x -> do
    ty <- view (context . at x)
    maybe (throwError TypeError) pure ty
  Abs bndr ty1 trm ->
    kindcheck ty1 >>= \case
      Star -> do
        ty2 <- local (context %~ M.insert bndr ty1) (typecheck trm)
        pure $ ty1 :-> ty2
      _ -> throwError KindError
  App t1 t2 -> do
    ty1 <- typecheck t1
    case ty1 of
      tyA :-> tyB -> do
        ty2 <- typecheck t2
        if unify [] tyA ty2 then pure tyB else throwError TypeError
      _ -> throwError TypeError
  TAbs x k t2 -> do
    ty2 <- local (contextT %~ M.insert x k) (typecheck t2)
    pure $ Forall x k ty2
  TApp t1 ty2 ->
    typecheck t1 >>= \case
      Forall x k1 ty12 ->
        kindcheck ty2 >>= \k2 ->
          if k1 == k2 then pure $ substT x ty2 ty12 else throwError TypeError
      _ -> throwError TypeError
  Unit -> pure UnitT
  T -> pure BoolT
  F -> pure BoolT
  If t0 t1 t2 -> do
    ty0 <- typecheck t0
    ty1 <- typecheck t1
    ty2 <- typecheck t2
    if ty0 == BoolT && ty1 == ty2
      then pure ty1
      else throwError TypeError

--------------------
--- Substitution ---
--------------------

substTyTm :: String -> Type -> Term -> Term
substTyTm x s = \case
  Abs y ty t1 -> Abs y (substT x s ty) t1
  App t1 t2 -> App (substTyTm x s t1) (substTyTm x s t2)
  If t0 t1 t2 -> If (substTyTm x s t0) (substTyTm x s t1) (substTyTm x s t2)
  t -> t

substT :: String -> Type -> Type -> Type
substT x s = \case
  TVar x' | x == x' -> s
  TVar y ->  TVar y
  TyAbs y k ty | x /= y -> TyAbs y k (substT x s ty)
  TyAbs y k ty -> error "substT: oops name collision"
  TyApp ty1 ty2 -> TyApp (substT x s ty1) (substT x s ty2)
  Forall y k ty | x /= y -> Forall y k (substT x s ty)
  ty1 :-> ty2 -> substT x s ty1 :-> substT x s ty2
  ty -> ty

subst :: String -> Term -> Term -> Term
subst x s = \case
  Var x' | x == x' -> s
  Var y -> Var y
  Abs y ty t1 | x /= y && y `notElem` freevars s -> Abs y ty (subst x s t1)
            | otherwise -> error "subst: oops name collision"
  App t1 t2 -> App (subst x s t1) (subst x s t2)
  TApp t0 ty -> TApp (subst x s t0) ty
  TAbs bndr k t0 -> TAbs bndr k (subst x s t0)
  If t0 t1 t2 -> If (subst x s t0) (subst x s t1) (subst x s t2)
  T -> T
  F -> F
  Unit -> Unit

freevars :: Term -> [String]
freevars = \case
  Var x       -> [x]
  Abs x ty t  -> freevars t \\ [x]
  App t1 t2   -> freevars t1 ++ freevars t2
  If t0 t1 t2 -> freevars t0 ++ freevars t1 ++ freevars t2
  TAbs x k t0 -> freevars t0
  TApp t0 ty  -> freevars t0
  _ -> []

------------------
--- Evaluation ---
------------------

isVal :: Term -> Bool
isVal = \case
  Abs{}  -> True
  TAbs{} -> True
  T      -> True
  F      -> True
  Unit   -> True
  _      -> False

singleEval :: Term -> Maybe Term
singleEval = \case
  App (Abs x ty t12) v2 | isVal v2 -> Just $ subst x v2 t12
  App v1@Abs{} t2 -> App v1 <$> singleEval t2
  App t1 t2 -> flip App t2 <$> singleEval t1
  TApp (TAbs x k t12) ty2 -> Just (substTyTm x ty2 t12)
  TApp t1 ty2 -> flip TApp ty2 <$> singleEval t1
  If T t2 t3 -> pure t2
  If F t2 t3 -> pure t3
  _ -> Nothing

multiStepEval :: Term -> Term
multiStepEval t = maybe t multiStepEval (singleEval t)

------------
--- Main ---
------------

-- Type Operators
idT :: Type
idT = TyAbs "A" Star $ Forall "Id" Star $ TVar "A" :-> TVar "X"

constT :: Type
constT = TyAbs "A" Star $ TyAbs "B" Star $ Forall "Const" Star $ TVar "A" :-> TVar "X"

pairT :: Type
pairT = TyAbs "A" Star $ TyAbs "B" Star $ Forall "C" Star $ (TVar "A" :-> TVar "B" :-> TVar "C") :-> TVar "C"

churchT :: Type
churchT = Forall "A" Star $ (TVar "A" :-> TVar "A") :-> TVar "A" :-> TVar "A"

-- Terms
--mkId :: Term
--mkId = TAbs "A" Star $ Abs "a" k

--pair = ΛA::*.ΛB::*.λx:A.λy:B.ΛC::*.λk:(A -> B -> C).k x y;
pair :: Term
pair = TAbs "A" Star $ TAbs "B" Star $
         Abs "x" (TVar "A") $ Abs "y" (TVar "B") $ TAbs "C" Star $
           Abs "k" (TVar "A" :-> TVar "B" :-> TVar "C") $
             App (App (Var "k") (Var "x")) (Var "y")

-- fst = ΛA::*.ΛB::*.λp:Pair A B.p [A] (λx:A.λy:B.x);
fst' = TAbs "A" Star $ TAbs "B" Star $
         Abs "p" (TyApp (TyApp pairT (TVar "A")) (TVar "B")) $
           App (TApp (Var "p") (TVar "A")) (Abs "x" (TVar "A") $ Abs "y" (TVar "B") (Var "x"))

zeroT :: Term
zeroT =  TAbs "F" Star $ Abs "f" (TVar "F") $ TAbs "X" Star $
  Abs "x" (TVar "X") $ App (TApp (Var "f") (TVar "X")) (App (Var "f") (Var "x"))

main :: IO ()
main =
  let term = alphaconvert $ (TApp (App pair T) BoolT)-- (App notT T)
  in case runTypecheckM $ typecheck term of
    Left e -> print e
    Right _ -> print (multiStepEval term)

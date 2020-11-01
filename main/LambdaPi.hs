{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
module Main where

import Data.Map (Map)
import qualified Data.Map.Strict as M
import Data.List ((\\))
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except

import Debug.Trace

-------------
--- Terms ---
-------------

type Name = String

data Term
  = Var Name
  | Universe Int
  | Pi Name Term Term
  | Abs Name Term Term
  | App Term Term
  | Sigma Name Term Term
  deriving (Show, Eq)

type Gamma = [(String, (Term, Maybe Term))]

extend :: Name -> (Term, Maybe Term) -> Gamma -> Gamma
extend bndr t gamma = (bndr, t) : gamma

lookupType :: Name -> Gamma -> Maybe Term
lookupType name gamma = fst <$> lookup name gamma

lookupValue :: Name -> Gamma -> Maybe Term
lookupValue name gamma = snd =<< lookup name gamma

----------------------
--- Pretty Printer ---
----------------------

class Show a => Pretty a where
  pretty :: a -> String
  pretty = show

instance Pretty Term where
  pretty = \case
    Var x -> x
    App t1 t2 -> pretty t1 ++ " " ++ pretty t2
    Abs bndr ty t0 -> "(λ" ++ bndr ++ " : " ++ pretty ty ++ ". " ++ pretty t0 ++ ")"
    Pi bndr t1 t2 -> "(Π" ++ bndr ++ " : " ++ pretty t1 ++ ". " ++ pretty t2 ++ ")"
    Universe k -> "Type" ++ show k

------------------------
--- Alpha Conversion ---
------------------------

data Stream a = Stream a (Stream a)

data AlphaContext = AlphaContext
  { _names :: Stream String
  , _register :: Map String String
  }

names :: [String]
names = (pure <$> ['a'..'z']) ++ (flip (:) <$> (show <$> [1..]) <*> ['a' .. 'z'])

stream :: [String] -> Stream String
stream (x:xs) = Stream x (stream xs)

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
  t@(Abs bndr ty term) -> do
    Stream fresh rest <- gets _names
    registry <- gets _register
    ty' <- alpha ty
    put $ AlphaContext rest (M.insert bndr fresh registry)
    term' <- alpha term
    pure $ Abs fresh ty' term'
  t@(Pi bndr ty1 ty2) -> do
    Stream fresh rest <- gets _names
    registry <- gets _register
    ty1' <- alpha ty1
    put $ AlphaContext rest (M.insert bndr fresh registry)
    ty2' <- alpha ty2
    pure $ Pi fresh ty1' ty2'
  t@(Sigma bndr ty1 ty2) -> do
    Stream fresh rest <- gets _names
    registry <- gets _register
    ty1' <- alpha ty1
    put $ AlphaContext rest (M.insert bndr fresh registry)
    ty2' <- alpha ty2
    pure $ Sigma fresh ty1' ty2'
  t -> pure t

emptyContext :: AlphaContext
emptyContext = AlphaContext (stream names) (M.empty)

alphaconvert :: Term -> Term
alphaconvert term = evalState (alpha term) emptyContext

--------------------
--- Typechecking ---
--------------------

data TypeErr = TypeError deriving (Show, Eq)

newtype InferM a =
  InferM { unInferM :: ExceptT TypeErr (Reader Gamma) a }
  deriving (Functor, Applicative, Monad, MonadReader Gamma, MonadError TypeErr)

runInferM :: InferM a -> Either TypeErr a
runInferM = flip runReader [] . runExceptT . unInferM

infer :: Term -> InferM Term
infer = \case
  Var x -> asks (lookupType x) >>= maybe (throwError TypeError) pure
  App t1 t2 ->
    infer t1 >>= normalize >>= \case
      Pi bndr ty1 ty2 -> do
          ty1' <- infer t2
          isEqual <- equal ty1 ty1'
          if isEqual
             then pure $ subst bndr t2 ty2
             else throwError TypeError
      _ -> throwError TypeError
  Abs bndr ty t -> do
    inferUniverse ty
    t' <- local (extend bndr (ty, Nothing)) (infer t)
    pure $ Pi bndr ty t'
  Pi bndr t1 t2 -> do
    k1 <- inferUniverse t1
    k2 <- local (extend bndr (t1, Nothing)) (inferUniverse t2)
    pure $ Universe (max k1 k2)
  Sigma bndr t1 t2 -> do
    k1 <- inferUniverse t1
    k2 <- inferUniverse t2
    pure $ Universe (max k1 k2)
  Universe k -> pure $ Universe (k + 1)

inferUniverse :: Term -> InferM Int
inferUniverse t =
  infer t >>= normalize >>= \case
    Universe k -> pure k
    _ -> throwError TypeError

equal :: Term -> Term -> InferM Bool
equal e1 e2 =
  case (e1, e2) of
    (Var x, Var y) -> pure $ x == y
    (App t1 t2, App t1' t2') -> (&&) <$> equal t1 t1' <*> equal t2 t2'
    (Universe k, Universe k') -> pure $ k == k'
    (Pi bndr t1 t2, Pi bndr' t1' t2') ->
      if t1 == t1'
         then equal t2 (subst bndr' (Var bndr) t2')
         else pure False
    (Abs bndr ty t, Abs bndr' ty' t') ->
      if ty == ty'
         then equal t (subst bndr' (Var bndr) t')
         else pure False
    (Sigma bndr t1 t2, Sigma bndr' t1' t2') ->
      if t1 == t1'
         then equal t2 (subst bndr' (Var bndr) t2')
         else pure False
    _ -> pure False

---------------------
--- Normalization ---
---------------------

normalize :: Term -> InferM Term
normalize t = case t of
  Var x -> asks (lookupValue x) >>= maybe (pure t) normalize
  App t1 t2 -> do
    t2' <- normalize t2
    normalize t1 >>= \case
      Abs bndr _ t -> normalize (subst bndr t2' t)
      t1' -> pure $ App t1' t2'
  Abs bndr ty t -> do
    ty' <- normalize ty
    t' <- local (extend bndr (ty, Nothing)) (normalize t)
    pure $ Abs bndr ty' t'
  Pi bndr t1 t2 -> do
    t1' <- normalize t1
    t2' <- local (extend bndr (t1, Nothing)) (normalize t2)
    pure $ Pi bndr t1' t2'
  Sigma bndr t1 t2 -> do
    t1' <- normalize t1
    t2' <- local (extend bndr (t1, Nothing)) (normalize t2)
    pure $ Sigma bndr t1' t2'
  t -> pure t

--------------------
--- Substitution ---
--------------------

subst :: String -> Term -> Term -> Term
subst x s = \case
  Var x' | x == x' -> s
  Var y -> Var y
  App t1 t2 -> App (subst x s t1) (subst x s t2)
  Abs y ty t1 | x /= y && y `notElem` freevars s -> Abs y (subst x s ty) (subst x s t1)
              | otherwise -> error "oops name collision"
  Pi y t1 t2 | x /= y && y `notElem` freevars s -> Pi y (subst x s t1) (subst x s t2)
              | otherwise -> error "oops name collision"
  Universe k -> Universe k

freevars :: Term -> [String]
freevars = \case
    Var x -> [x]
    Abs x ty t -> freevars ty ++ (freevars t \\ [x])
    Pi x t1 t2 -> freevars t1 ++ (freevars t2 \\ [x])
    App t1 t2 -> freevars t1 ++ freevars t2
    Universe k -> []

--------------------
--- Sample Terms ---
--------------------

identity :: Int -> Term
identity n = Abs "A" (Universe n) (Abs "x" (Var "A") (Var "x"))

identityType :: Int -> Term
identityType n = (Pi "B" (Universe n) (Pi "y" (Var "B") (Var "B")))

appTest :: Term
appTest = App (App (identity 1) (identityType 0)) (identity 0)

constant :: Term
constant =
  Abs "A" (Universe 0) $ Abs "B" (Universe 0) $
    Abs "x" (Var "A") $ Abs "y" (Var "B") (Var "x")

------------
--- Main ---
------------

check :: Term -> Either TypeErr String
check = runInferM . fmap pretty . infer

main :: IO ()
main = do
  let t = alphaconvert appTest
  print t
  mapM_ putStrLn (check t)

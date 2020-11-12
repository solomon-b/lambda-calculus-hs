{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
module Main where

import Data.Foldable
import qualified Data.List.NonEmpty as NEL
import Data.List.NonEmpty (NonEmpty(..))
import Data.List (foldl', foldl1')
import Data.Map (Map)
import qualified Data.Map.Strict as M
import Data.List ((\\), sort)
import Control.Lens hiding (Context)
import Control.Monad
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except

-------------
--- Terms ---
-------------

type Tycon = String
type Binding = String

data Term =
    Var Binding
  | Abs Binding Type Term
  | App Term Term
  | Constructor String
  | Case Term [(NonEmpty String, Term)]
  deriving Show

data Type = Type :-> Type | TypeConstructor String
  deriving (Show, Eq)

data DataConstructor = DataConstructor
  { _typeConstructorName :: String
  , _dataConstructors    :: [(String, [Type])]
  } deriving Show
makeLenses ''DataConstructor

data Context = Context
  { _gamma :: Map Binding Type
  , _dataDeclarations :: Map Tycon DataConstructor
  , _valueDeclarations :: Map Binding Term
  } deriving Show
makeLenses ''Context

emptyContext :: Context
emptyContext = Context M.empty M.empty M.empty

data TypeErr = TypeError deriving (Show, Eq)

------------------------
--- Alpha Conversion ---
------------------------

data Stream a = Stream a (Stream a)

data AlphaContext = AlphaContext { _names :: Stream String, _register :: Map String String }

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
      Nothing -> pure $ Var x
  App t1 t2 -> do
    t1' <- alpha t1
    t2' <- alpha t2
    pure $ App t1' t2'
  t@(Abs bndr ty term) -> do
    (Stream fresh rest) <- gets _names
    registry <- gets _register
    put $ AlphaContext rest (M.insert bndr fresh registry)
    term' <- alpha term
    pure $ Abs fresh ty term'
  Case t1 patterns -> do
    t1' <- alpha t1
    patterns' <- (traverse . traverse) alpha patterns
    pure $ Case t1' patterns'
  t -> pure t

emptyAlphaContext :: AlphaContext
emptyAlphaContext = AlphaContext (stream names) (M.empty)

alphaconvert :: Term -> Term
alphaconvert term = evalState (alpha term) emptyAlphaContext

--------------------
--- Typechecking ---
--------------------

newtype TypecheckM a =
  TypecheckM { unTypecheckM :: ExceptT TypeErr (Reader Context) a }
  deriving (Functor, Applicative, Monad, MonadReader Context, MonadError TypeErr)

extendTypecheckM :: Context -> TypecheckM a -> Either TypeErr a
extendTypecheckM gamma = flip runReader gamma . runExceptT . unTypecheckM

runTypecheckM :: TypecheckM a -> Either TypeErr a
runTypecheckM = flip runReader emptyContext . runExceptT . unTypecheckM

typecheck :: Term -> TypecheckM Type
typecheck = \case
  Var x -> do
    ty <- view (gamma . at x)
    maybe (throwError TypeError) pure ty
  Abs bndr ty1 trm -> do
    ty2 <- local (gamma %~ M.insert bndr ty1) (typecheck trm)
    pure $ ty1 :-> ty2
  App t1 t2 -> do
    ty1 <- typecheck t1
    case ty1 of
      tyA :-> tyB -> do
        ty2 <- typecheck t2
        if tyA == ty2 then pure tyB else throwError TypeError
      _ -> throwError TypeError
  Constructor cnstr -> do
    tycon <- view (gamma . at cnstr)
    g <- view gamma
    maybe (throwError TypeError) pure tycon
  Case t1 patterns ->
    typecheck t1 >>= \case
      TypeConstructor tycon -> do
        view (dataDeclarations . at tycon) >>= \case
          Just decl -> do
            let consTags = sort $ decl ^.. dataConstructors . folded . _1
                pattTags = sort $ NEL.head <$> patterns ^.. folded . _1
            if consTags == pattTags
               then checkPatterns decl patterns
               else throwError TypeError
          Nothing -> throwError TypeError
      _ -> throwError TypeError

checkPattern :: DataConstructor -> (NonEmpty String, Term) -> TypecheckM Type
checkPattern decl (cnstr :| xs, term) = do
  let cnstrs = decl ^. dataConstructors
  case lookup cnstr cnstrs of
    Just ys ->
      if length xs == length ys
         then local (gamma %~ (`M.union` M.fromList (zip xs ys))) (typecheck term)
         else throwError TypeError
    Nothing -> throwError TypeError

checkPatterns :: DataConstructor -> [(NonEmpty String, Term)] -> TypecheckM Type
checkPatterns decl patterns = do
  traverse (checkPattern decl) patterns >>= \case
    [] -> throwError TypeError
    (x:xs) -> if all (== x) xs
                 then pure x
                 else throwError TypeError

--------------------
--- Substitution ---
--------------------

subst :: String -> Term -> Term -> Term
subst x s = \case
  (Var x') | x == x' -> s
  (Var y) -> Var y
  (Abs y ty t1) | x /= y && y `notElem` freevars s -> Abs y ty (subst x s t1)
                | otherwise -> error "oops name collision"
  (App t1 t2) -> App (subst x s t1) (subst x s t2)
  Constructor cstr -> Constructor cstr
  Case t1 pattrns -> Case (subst x s t1) (fmap (subst x s) <$> pattrns)

freevars :: Term -> [String]
freevars = \case
  Var x       -> [x]
  Abs x ty t  -> freevars t \\ [x]
  App t1 t2   -> freevars t1 ++ freevars t2
  Constructor x -> [x]
  Case t1 pattrns -> freevars t1 ++ concatMapOf (folded . _2) freevars pattrns

------------------
--- Evaluation ---
------------------

isVal :: Term -> Bool
isVal = \case
  Abs{} -> True
  Constructor x -> True
  _     -> False

singleEval :: Term -> Maybe Term
singleEval = \case
  App (Abs x ty t12) v2 | isVal v2 -> Just $ subst x v2 t12
  App v1@Abs{} t2 -> App v1 <$> singleEval t2
  App t1 t2 -> flip App t2 <$> singleEval t1
  Case v1 pattrns | isVal v1 -> match v1 pattrns
  Case t1 pattrns -> flip Case pattrns <$> singleEval t1
  _ -> Nothing

match :: Term -> [(NonEmpty String, Term)] -> Maybe Term
match (Constructor cnstr) pattrns =
  let xs = map (\(x:|xs, y) -> (x, y)) pattrns
  in lookup cnstr xs
match _ pattrns = Nothing

multiStepEval :: Term -> Term
multiStepEval t = maybe t multiStepEval (singleEval t)

---------------
--- Modules ---
---------------

data Module = Module { declarations :: [(String, Term)] }
  deriving Show

checkDecl :: (String, Term) -> TypecheckM (String, (Type, Maybe Term))
checkDecl (bndr, term) = do
  ty <- typecheck term
  pure (bndr, (ty, Just term))

--checkModule :: Module -> StateT Gamma TypecheckM ()
--checkModule (Module xs) = forM_ xs $ \x -> do
--    gamma <- get
--    (bndr, (ty, term)) <- lift $ local (const gamma) (checkDecl x)
--    modify (extendTerm bndr ty term)

--runCheckModule :: Module -> Either TypeErr ()
--runCheckModule mod = runTypecheckM $ evalStateT (checkModule mod) M.empty

inlineTerms :: [(String, Term)] -> Term -> Term
inlineTerms xs term =
  let f term (x, t) = case term of
        Var x' | x == x' -> t
        Abs bndr ty t1 -> Abs bndr ty (f t1 (x, t))
        App t1 t2 -> App (f t1 (x, t)) (f t2 (x, t))
        t -> t
  in foldl' f term xs

data Zipper a = Z [a] a [a]
  deriving Show

inlineModule :: Module -> Term
inlineModule (Module [x]) = snd x
inlineModule (Module (x:xs)) =
  let f (Z left curr []) = inlineTerms left (snd curr)
      f (Z left curr (r:ight)) = f $ Z ((inlineTerms left <$> curr) : left) r ight
  in f $ Z [] x xs

execModule :: Module -> Either TypeErr Term
execModule m@(Module decls) =
  let main = inlineModule (Module (fmap alphaconvert <$> decls))
  in undefined -- runCheckModule m >> pure (multiStepEval main)

------------
--- Main ---
------------

notT :: Term
notT =
  Abs "p" (TypeConstructor "Boolean") $
    Case (Var "p") [ ("True" :| [], Constructor "False")
                   , ("False" :| [], Constructor "True")
                   ]

boolDec :: DataConstructor
boolDec = DataConstructor
  { _typeConstructorName = "Boolean"
  , _dataConstructors    = [("True", []) , ("False", [])]
  }

idBoolDec :: DataConstructor
idBoolDec = DataConstructor
  { _typeConstructorName = "IdT"
  , _dataConstructors = [("Id", [TypeConstructor "Boolean"])]
  }

testContext :: Context
testContext = Context g d f
  where
    g = M.fromList [ ("Id", (TypeConstructor "Boolean" :-> TypeConstructor "IdT"))
                   , ("True", TypeConstructor "Boolean")
                   , ("False", TypeConstructor "Boolean")
                   ]
    d = M.fromList [ ("Boolean", (DataConstructor "Boolean" [("True", []), ("False", [])]))
                   , ("IdT", (DataConstructor "IdT" [("Id", [TypeConstructor "Boolean"])]))
                   ]
    f = M.empty

caseTest :: Term
caseTest =
  Abs "x" (TypeConstructor "IdT") $
    Case (Var "x") [("Id" :| ["y"], Var "y")]

main :: IO ()
main = do
  let term = App notT (Constructor "True")
  print $ extendTypecheckM testContext (typecheck term)
  print $ multiStepEval term

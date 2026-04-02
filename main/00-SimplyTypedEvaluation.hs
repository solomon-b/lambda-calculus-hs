-- | Simply Typed Lambda Calculus, evaluation only.
--
-- This is the baseline implementation that all subsequent modules build on. We
-- define a small language with functions, pairs, and unit, then build an
-- evaluator that reduces terms to values using closures and de Bruijn indices.
--
-- There is no typechecker here. Terms carry type annotations but we don't
-- verify them. The focus is on the evaluation model: how closures capture their
-- environment, how de Bruijn indices avoid the need for capture-avoiding
-- substitution, and how application triggers beta reduction by extending a
-- closure's captured environment.
module Main where

--------------------------------------------------------------------------------

import Data.Maybe (fromMaybe)
import Data.String

--------------------------------------------------------------------------------
-- Utils

-- | A list that grows on the right. We use this as our environment
-- representation because it matches the structure of de Bruijn indices: the
-- most recently bound variable is at the end (index 0), and older bindings are
-- further left (higher indices).
--
-- A regular list would work too, but snoc lists make the correspondence between
-- binding order and index explicit.
data SnocList a
  = Snoc (SnocList a) a
  | Nil
  deriving (Show, Eq, Ord, Functor, Foldable)

-- | Look up a value by de Bruijn index, counting from the right (most recent
-- binding).
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
-- Syntax
--
-- Our language has two representations:
--
--   - 'Term' - what the programmer writes.
--   - 'Value' - what evaluation produces.
--
-- A 'Lam' in the syntax becomes a 'VLam' closure that captures its environment,
-- deferring substitution until thefunction is applied.

-- | The abstract syntax tree of our language.
--
-- Variables use de Bruijn indices ('Ix') rather than names, which makes
-- alpha-equivalence trivial (syntactic equality) at the cost of human
-- readability.
data Term
  = -- | A variable reference by de Bruijn index. @x@
    Var Ix
  | -- | Lambda abstraction. @\x. body@
    Lam Name Term
  | -- | Function application. @f x@
    Ap Term Term
  | -- | Pair introduction. @(a, b)@
    Pair Term Term
  | -- | First projection of a pair. @fst p@
    Fst Term
  | -- | Second projection of a pair. @snd p@
    Snd Term
  | -- | The unit value. @()@
    Unit
  | -- | A term with a type annotation that we ignore during evaluation. @(t : A)@
    Anno Type Term
  deriving stock (Show, Eq, Ord)

-- | The type language.
--
-- At this point we have no type inference, so every lambda needs an annotation
-- (via 'Anno') to tell us its type. We have function types, pair types, and the
-- unit type.
data Type
  = -- | Function type. @A -> B@.
    FuncTy Type Type
  | -- | Pair type. @A * B@.
    PairTy Type Type
  | -- | Unit type. @Unit@.
    UnitTy
  deriving stock (Show, Eq, Ord)

-- | The result of evaluation.
--
-- The key difference from 'Term' is that lambdas become 'VLam' closures that
-- pair the function body with the environment it was defined in.
--
-- This is how we avoid substitution, instead of replacing variables in the
-- body, we record what they should evaluate to in the closure's environment and
-- look them up at use sites.
data Value
  = -- | A closure: the lambda body paired with its defining environment.
    -- Application triggers beta reduction by extending this environment.
    VLam Name Closure
  | -- | A fully evaluated pair of values.
    VPair Value Value
  | -- | The unit value.
    VUnit
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

newtype Name = Name {getName :: String}
  deriving newtype (Show, Eq, Ord, IsString)

-- | A closure pairs a function body with the environment it was defined in.
-- When we evaluate @λx. body@ in environment @env@, we don't substitute into
-- @body@, we store @(env, body)@ as a 'Closure'. Later, when the function is
-- applied to an argument @v@, we evaluate @body@ in @Snoc env v@: the original
-- environment extended with the argument.
--
-- This "substitution by environment extension" is the core trick that makes
-- evaluation efficient. It turns substitution (a traversal of the entire term)
-- into a constant-time environment push.
data Closure = Closure {env :: SnocList Value, body :: Term}
  deriving stock (Show, Eq, Ord)

--------------------------------------------------------------------------------
-- Evaluator
--
-- Evaluation maps 'Term' to 'Value' under an environment. The interesting cases
-- are:
--
-- - 'Var': look up the value in the environment by de Bruijn index.
-- - 'Lam': capture the current environment in a closure (don't evaluate the
--          body yet, since we don't know the argument).
-- - 'Ap': evaluate both sides, then apply. This is where beta reduction
--         happens, by instantiating the closure with the argument.

-- | Evaluate a term to a value under the given environment.
eval :: SnocList Value -> Term -> Value
eval env = \case
  Var (Ix ix) -> fromMaybe (error "internal error") $ nth env ix
  Lam bndr body -> VLam bndr (Closure env body)
  Ap tm1 tm2 ->
    let fun = eval env tm1
        arg = eval env tm2
     in doApply fun arg
  Pair tm1 tm2 ->
    let tm1' = eval env tm1
        tm2' = eval env tm2
     in VPair tm1' tm2'
  Fst tm -> doFst $ eval env tm
  Snd tm -> doSnd $ eval env tm
  Anno _ty tm -> eval env tm
  Unit -> VUnit

-- | Apply a function value to an argument. This is beta reduction: @(λx. body)
-- arg@ becomes @body@ evaluated in the closure's captured environment extended
-- with @arg@.
doApply :: Value -> Value -> Value
doApply (VLam _ clo) arg = instantiateClosure clo arg
doApply _ _ = error "impossible case in doApply"

doFst :: Value -> Value
doFst (VPair a _b) = a
doFst _ = error "impossible case in doFst"

doSnd :: Value -> Value
doSnd (VPair _a b) = b
doSnd _ = error "impossible case in doSnd"

-- | Instantiate a closure by extending its captured environment with the
-- argument value, then evaluating the body.
--
-- This is the key operation: substitution is replaced by a constant-time
-- 'Snoc', and the actual lookup happens lazily when we hit a 'Var' during
-- evaluation of the body.
instantiateClosure :: Closure -> Value -> Value
instantiateClosure (Closure env body) v = eval (Snoc env v) body

--------------------------------------------------------------------------------
-- Main

run :: Term -> Value
run = eval Nil

main :: IO ()
main = print $ run (Ap idenT' Unit)

-- λx. x
idenT :: Term
idenT =
  Anno
    (UnitTy `FuncTy` UnitTy)
    (Lam (Name "x") (Var (Ix 0)))

-- λf. f
idenT' :: Term
idenT' =
  Anno
    ((UnitTy `FuncTy` UnitTy) `FuncTy` (UnitTy `FuncTy` UnitTy))
    (Lam (Name "f") (Var (Ix 0)))

-- λx. λy. x
constT :: Term
constT =
  Anno
    (UnitTy `FuncTy` (UnitTy `FuncTy` UnitTy))
    (Lam (Name "x") (Lam (Name "_") (Var (Ix 1))))

-- λf. λx. f x
applyT :: Term
applyT =
  Anno
    ((UnitTy `FuncTy` UnitTy) `FuncTy` (UnitTy `FuncTy` UnitTy))
    (Lam (Name "f") (Lam (Name "x") (Ap (Var (Ix 1)) (Var (Ix 0)))))

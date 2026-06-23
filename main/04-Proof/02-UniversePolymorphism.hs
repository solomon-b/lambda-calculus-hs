{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- | Martin-Löf Type Theory with universe polymorphism.
--
-- Extends module 12 (Type Universes) by replacing concrete universe levels with
-- a level expression language that supports level variables, @max@, and @succ@.
--
-- This enables universe-polymorphic definitions like @id : forall l. (a : Type
-- l) -> a -> a@.
--
-- Levels are a separate sort with their own de Bruijn index space, following
-- the System F precedent in module 10. Level quantification (@forall l. A@)
-- lives at @Type omega_0@, a special level above all finite levels. Omega
-- levels form their own hierarchy (@Type omega_0 : Type omega_1 : ...@) to
-- avoid circularity. Level comparison is structural and conservative (sound but
-- incomplete).
module Main where

--------------------------------------------------------------------------------

import Control.Arrow ((&&&))
import Control.Monad (foldM, forM, when, zipWithM)
import Control.Monad.Except (MonadError (..))
import Control.Monad.Identity
import Control.Monad.Reader (MonadReader (..), asks)
import Control.Monad.Trans.Except (ExceptT (..))
import Control.Monad.Trans.Reader (Reader, ReaderT (..))
import Control.Monad.Trans.Writer.Strict (WriterT (..))
import Control.Monad.Writer.Strict (MonadWriter (..))
import Data.Foldable (find)
import Data.Map (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Scientific (Scientific)
import Data.String
import Data.These
import Numeric.Natural (Natural)
import PrettyTerm (Prec, appPrec, arrowPrec, arrowSym, atomPrec, bigLambdaSym, forallSym, lamPrec, lambdaSym, parensIf, sumPrec)
import PrettyTerm qualified as PP
import TestHarness (RunResult (..), runTest, runTestErr, section)
import Utils (SnocList (..), alignWithM, allM, nth)

--------------------------------------------------------------------------------
-- Syntax
--
-- We use a three-level representation. Unlike System F, each level
-- is a single unified type covering both terms and types.
--
-- 1. 'Term': surface syntax with named variables.
-- 2. 'Syntax': core IR with de Bruijn indices, produced by
--    elaboration.
-- 3. 'Value': semantic domain with closures and neutrals,
--    produced by evaluation.
--
-- 'Term' uses named variables ('Name') instead of de Bruijn
-- indices. The typechecker resolves names to indices during
-- elaboration, producing 'Syntax'. This means typechecking and
-- elaboration happen in a single pass.

-- | Surface syntax with named variables. The programmer writes @λx. x@ and
-- elaboration resolves @x@ to the appropriate de Bruijn index.
data Term
  = -- | A variable reference by name. @x@
    Var Name
  | -- | Lambda abstraction. @\x. body@
    Lam Name Term
  | -- | Function application. @f x@
    Ap Term Term
  | -- | Let binding. @let x = t1 in t2@
    Let Name Term Term
  | -- | A term with a type annotation. @(t : A)@
    Anno Term Term
  | -- | A missing subterm. Can only appear in check position
    -- (where the expected type is known).
    Hole
  | -- | The universe of types at a given level.
    -- @Type n : Type (n + 1)@.
    Univ Level
  | -- | Dependent function type. @(x : A) -> B@. Binds a
    -- variable in the codomain. Non-dependent functions use
    -- 'FuncTy' as sugar.
    Pi Name Term Term
  | -- | Non-dependent function type. @A -> B@.
    FuncTy Term Term
  | -- | Level quantification. @forall l. A@. Binds a level
    -- variable in the body.
    LevelPi Name Term
  | -- | Level abstraction. @/\l. body@.
    LevelLam Name Term
  | -- | Level application. The second argument is a 'Level'
    -- expression, not a 'Term'.
    LevelAp Term Level
  | -- | Dependent pair type. @(x : A) * B@. Binds a variable
    -- in the second component's type. Non-dependent pairs use
    -- 'PairTy' as sugar.
    Sigma Name Term Term
  | -- | Non-dependent pair type. @A * B@.
    PairTy Term Term
  | -- | Pair introduction. @(a, b)@
    Pair Term Term
  | -- | First projection of a pair. @fst p@
    Fst Term
  | -- | Second projection of a pair. @snd p@
    Snd Term
  | -- | Bool type. @Bool@.
    BoolTy
  | -- | Boolean true. @true@
    Tru
  | -- | Boolean false. @false@
    Fls
  | -- | Conditional. @if scrut then t else f@
    If Term Term Term
  | -- | Unit type. @Unit@.
    UnitTy
  | -- | The unit value. @()@
    Unit
  | -- | The empty type. No values inhabit it.
    VoidTy
  | -- | Void elimination. Can produce any type from a value
    -- of type 'Void', since no such value exists.
    Absurd Term
  | -- | Binary sum type. @A + B@.
    SumTy Term Term
  | -- | Left injection into a sum type.
    InL Term
  | -- | Right injection into a sum type.
    InR Term
  | -- | Binary sum elimination. Binds a variable in each
    -- branch.
    SumCase Term (Name, Term) (Name, Term)
  | -- | Natural number type. @Nat@. Subtype of 'IntegerTy'.
    NaturalTy
  | -- | Integer type. @Int@. Subtype of 'RealTy'.
    IntegerTy
  | -- | Real number type. @Real@. Top of the numeric tower.
    RealTy
  | -- | A natural number literal.
    Natural Integer
  | -- | An integer literal.
    Integer Integer
  | -- | A real number literal.
    Real Scientific
  | -- | A record type: a list of named fields with their
    -- types.
    RecordTy [(Name, Term)]
  | -- | A record literal: a list of named fields with values.
    Record [(Name, Term)]
  | -- | Field projection from a record.
    Get Name Term
  | -- | A nominal inductive type, referenced by name.
    AdtTy Name [Term]
  | -- | Apply a named data constructor to arguments.
    Cnstr Name [Term]
  | -- | Pattern match on a nominal inductive type. Each
    -- branch names a constructor, binds its fields, and
    -- provides a body.
    Case Term [(Name, [Name], Term)]
  deriving stock (Show, Eq, Ord)

instance PP.Pretty Term where
  pretty = prettyTerm lamPrec

prettyLevel :: Level -> PP.Doc ann
prettyLevel (LNat n) = PP.pretty n
prettyLevel (LVar nm) = PP.pretty (getName nm)
prettyLevel (LMax a b) =
  "(" <> "max" PP.<+> prettyLevel a PP.<+> prettyLevel b <> ")"
prettyLevel (LSucc l) =
  "(" <> "succ" PP.<+> prettyLevel l <> ")"

prettyTerm :: Prec -> Term -> PP.Doc ann
prettyTerm _ (Var n) = PP.pretty (getName n)
prettyTerm p (Lam n body) =
  parensIf (p > lamPrec) $
    lambdaSym <> PP.pretty (getName n) <> "." PP.<+> prettyTerm lamPrec body
prettyTerm p (Ap f x) =
  parensIf (p > appPrec) $
    prettyTerm appPrec f PP.<+> prettyTerm atomPrec x
prettyTerm p (Let n rhs body) =
  parensIf (p > lamPrec) $
    "let"
      PP.<+> PP.pretty (getName n)
      PP.<+> "="
      PP.<+> prettyTerm lamPrec rhs
      PP.<+> "in"
      PP.<+> prettyTerm lamPrec body
prettyTerm p (Anno ty e) =
  parensIf (p > lamPrec) $
    prettyTerm (lamPrec + 1) e PP.<+> ":" PP.<+> prettyTerm lamPrec ty
prettyTerm _ Hole = "_"
prettyTerm p (Univ l) =
  parensIf (p > appPrec) $ "Type" PP.<+> prettyLevel l
prettyTerm p (Pi n a b) =
  parensIf (p > lamPrec) $
    "("
      <> PP.pretty (getName n)
        PP.<+> ":"
        PP.<+> prettyTerm lamPrec a
      <> ")"
        PP.<+> arrowSym
        PP.<+> prettyTerm lamPrec b
prettyTerm p (FuncTy a b) =
  parensIf (p > arrowPrec) $
    prettyTerm (arrowPrec + 1) a PP.<+> arrowSym PP.<+> prettyTerm arrowPrec b
prettyTerm p (LevelPi n body) =
  parensIf (p > lamPrec) $
    forallSym <> PP.pretty (getName n) <> "." PP.<+> prettyTerm lamPrec body
prettyTerm p (LevelLam n body) =
  parensIf (p > lamPrec) $
    bigLambdaSym <> PP.pretty (getName n) <> "." PP.<+> prettyTerm lamPrec body
prettyTerm p (LevelAp f l) =
  parensIf (p > appPrec) $
    prettyTerm appPrec f PP.<+> "@" <> prettyLevel l
prettyTerm p (Sigma n a b) =
  parensIf (p > lamPrec) $
    "("
      <> PP.pretty (getName n)
        PP.<+> ":"
        PP.<+> prettyTerm lamPrec a
      <> ")"
        PP.<+> "*"
        PP.<+> prettyTerm lamPrec b
prettyTerm p (PairTy a b) =
  parensIf (p > arrowPrec) $
    prettyTerm (arrowPrec + 1) a PP.<+> "*" PP.<+> prettyTerm arrowPrec b
prettyTerm p (Pair a b) =
  parensIf (p > lamPrec) $
    PP.tupled [prettyTerm lamPrec a, prettyTerm lamPrec b]
prettyTerm p (Fst e) =
  parensIf (p > appPrec) $
    "fst" PP.<+> prettyTerm atomPrec e
prettyTerm p (Snd e) =
  parensIf (p > appPrec) $
    "snd" PP.<+> prettyTerm atomPrec e
prettyTerm _ BoolTy = "Bool"
prettyTerm _ Tru = "True"
prettyTerm _ Fls = "False"
prettyTerm p (If scrut t f) =
  parensIf (p > lamPrec) $
    "if"
      PP.<+> prettyTerm lamPrec scrut
      PP.<+> "then"
      PP.<+> prettyTerm lamPrec t
      PP.<+> "else"
      PP.<+> prettyTerm lamPrec f
prettyTerm _ UnitTy = "Unit"
prettyTerm _ Unit = "()"
prettyTerm _ VoidTy = "Void"
prettyTerm p (Absurd e) =
  parensIf (p > appPrec) $
    "absurd" PP.<+> prettyTerm atomPrec e
prettyTerm p (SumTy a b) =
  parensIf (p > sumPrec) $
    prettyTerm (sumPrec + 1) a PP.<+> "+" PP.<+> prettyTerm sumPrec b
prettyTerm p (InL e) =
  parensIf (p > appPrec) $
    "inl" PP.<+> prettyTerm atomPrec e
prettyTerm p (InR e) =
  parensIf (p > appPrec) $
    "inr" PP.<+> prettyTerm atomPrec e
prettyTerm p (SumCase scrut (ln, l) (rn, r)) =
  parensIf (p > lamPrec) $
    "case"
      PP.<+> prettyTerm lamPrec scrut
      PP.<+> "of"
      PP.<+> "inl"
      PP.<+> PP.pretty (getName ln)
      PP.<+> arrowSym
      PP.<+> prettyTerm lamPrec l
      <> ";"
        PP.<+> "inr"
        PP.<+> PP.pretty (getName rn)
        PP.<+> arrowSym
        PP.<+> prettyTerm lamPrec r
prettyTerm _ NaturalTy = "Nat"
prettyTerm _ IntegerTy = "Int"
prettyTerm _ RealTy = "Real"
prettyTerm _ (Natural n) = PP.pretty n
prettyTerm _ (Integer n) = PP.pretty n
prettyTerm _ (Real n) = PP.pretty (show n)
prettyTerm _ (RecordTy fields) =
  PP.braces $
    PP.sep $
      PP.punctuate PP.comma $
        map (\(n, ty) -> PP.pretty (getName n) <> ":" PP.<+> prettyTerm lamPrec ty) fields
prettyTerm _ (Record fields) =
  PP.braces $
    PP.sep $
      PP.punctuate PP.comma $
        map (\(n, e) -> PP.pretty (getName n) PP.<+> "=" PP.<+> prettyTerm lamPrec e) fields
prettyTerm p (Get n e) =
  parensIf (p > appPrec) $
    prettyTerm atomPrec e <> "." <> PP.pretty (getName n)
prettyTerm _ (AdtTy n []) = PP.pretty (getName n)
prettyTerm p (AdtTy n tys) =
  parensIf (p > appPrec) $
    PP.pretty (getName n) PP.<+> PP.hsep (map (prettyTerm atomPrec) tys)
prettyTerm _ (Cnstr n []) = PP.pretty (getName n)
prettyTerm p (Cnstr n args) =
  parensIf (p > appPrec) $
    PP.pretty (getName n) PP.<+> PP.hsep (map (prettyTerm atomPrec) args)
prettyTerm p (Case scrut branches) =
  parensIf (p > lamPrec) $
    "case"
      PP.<+> prettyTerm lamPrec scrut
      PP.<+> "of"
      PP.<+> PP.sep
        ( PP.punctuate ";" $
            map
              ( \(cn, binds, body) ->
                  PP.pretty (getName cn)
                    PP.<+> PP.hsep (map (PP.pretty . getName) binds)
                    PP.<+> arrowSym
                    PP.<+> prettyTerm lamPrec body
              )
              branches
        )

-- | Core IR with de Bruijn indices.
--
-- This is what the evaluator operates on. Elaboration translates 'Term' into
-- 'Syntax', resolving named variables to indices and stripping away
-- annotations.
data Syntax
  = -- | A resolved variable reference by de Bruijn index.
    SVar (Ix Syntax)
  | -- | Lambda abstraction.
    SLam Name Syntax
  | -- | Function application.
    SAp Syntax Syntax
  | -- | A hole carrying the expected type. Evaluates to a
    -- neutral so it propagates through NbE.
    SHole Syntax
  | -- | The universe of types.
    SUniv SLevel
  | -- | Dependent function type. The body may reference the
    -- bound variable (index 0).
    SPi Name Syntax Syntax
  | -- | Non-dependent function type. @A -> B@.
    SFuncTy Syntax Syntax
  | -- | Level quantification. Binds a level variable (index
    -- 0 in the level namespace) in the body.
    SLevelPi Name Syntax
  | -- | Level abstraction.
    SLevelLam Name Syntax
  | -- | Level application. The argument is an 'SLevel', not
    -- a 'Syntax' term.
    SLevelAp Syntax SLevel
  | -- | Dependent pair type. The second component's type may
    -- reference the bound variable (index 0).
    SSigma Name Syntax Syntax
  | -- | Non-dependent pair type. @A * B@.
    SPairTy Syntax Syntax
  | -- | Pair introduction.
    SPair Syntax Syntax
  | -- | First projection of a pair.
    SFst Syntax
  | -- | Second projection of a pair.
    SSnd Syntax
  | -- | Bool type.
    SBoolTy
  | -- | Boolean true.
    STru
  | -- | Boolean false.
    SFls
  | -- | Conditional. @if scrut then t else f@.
    SIf Syntax Syntax Syntax Syntax
  | -- | Unit type.
    SUnitTy
  | -- | The unit value.
    SUnit
  | -- | The empty type.
    SVoidTy
  | -- | Elimination of the empty type. @absurd t@.
    SAbsurd Syntax Syntax
  | -- | Binary sum type. @A + B@.
    SSumTy Syntax Syntax
  | -- | Left injection into a sum type. @inl x@.
    SInL Syntax
  | -- | Right injection into a sum type. @inr x@.
    SInR Syntax
  | -- | Case analysis on a sum type.
    SSumCase Syntax Syntax Syntax Syntax
  | -- | Natural number type.
    SNaturalTy
  | -- | Integer type.
    SIntegerTy
  | -- | Real number type.
    SRealTy
  | -- | A natural number literal.
    SNatural Integer
  | -- | An integer literal.
    SInteger Integer
  | -- | A real number literal.
    SReal Scientific
  | -- | Record type.
    SRecordTy [(Name, Syntax)]
  | -- | Record introduction. A list of named fields.
    SRecord [(Name, Syntax)]
  | -- | Record field projection. @r.field@.
    SGet Name Syntax
  | -- | A nominal inductive type, referenced by name.
    SAdtTy Name [Syntax]
  | -- | A data constructor applied to its elaborated
    -- arguments.
    SCnstr Name [Syntax]
  | -- | Pattern match on a nominal inductive type. Each
    -- branch pairs a constructor name with an elaborated
    -- body (a lambda over the constructor's fields).
    SCase Syntax [(Name, Syntax)]
  deriving stock (Show, Eq, Ord)

-- | The result of evaluation.
--
-- The key difference from 'Syntax' is that lambdas become 'VLam' closures that
-- pair the function body with the environment it was defined in. Closures hold
-- 'Syntax' bodies, since the evaluator operates on the elaborated core IR.
--
-- This is how we avoid substitution, instead of replacing variables in the
-- body, we record what they should evaluate to in the closure's environment and
-- look them up at use sites.
data Value
  = -- | A stuck computation. A variable applied to eliminators
    -- that can't reduce. The 'Value' annotation records the
    -- type so quoting knows how to eta-expand.
    VNeutral Value Neutral
  | -- | A closure pairing a lambda body with its defining
    -- environment.
    VLam Name Closure
  | -- | The universe of types at a given level.
    -- @Type n : Type (n + 1)@.
    VUniv VLevel
  | -- | Dependent function type. The closure computes the
    -- codomain given a value of the domain type.
    VPi Name Value Closure
  | -- | Evaluated non-dependent function type.
    VFuncTy Value Value
  | -- | Level quantification. The 'LevelClosure' computes
    -- the body type given a level argument.
    VLevelPi Name LevelClosure
  | -- | Level abstraction as a 'LevelClosure'.
    VLevelLam Name LevelClosure
  | -- | Dependent pair type. The closure computes the second
    -- component's type given the first component's value.
    VSigma Name Value Closure
  | -- | Evaluated non-dependent pair type.
    VPairTy Value Value
  | -- | A fully evaluated pair of values.
    VPair Value Value
  | -- | Evaluated bool type.
    VBoolTy
  | -- | Boolean true.
    VTru
  | -- | Boolean false.
    VFls
  | -- | Evaluated unit type.
    VUnitTy
  | -- | The unit value.
    VUnit
  | -- | Evaluated void type.
    VVoidTy
  | -- | Evaluated sum type.
    VSumTy Value Value
  | -- | Left injection value.
    VInL Value
  | -- | Right injection value.
    VInR Value
  | -- | Evaluated natural number type.
    VNaturalTy
  | -- | Evaluated integer type.
    VIntegerTy
  | -- | Evaluated real number type.
    VRealTy
  | -- | A natural number value.
    VNatural Integer
  | -- | An integer value.
    VInteger Integer
  | -- | A real number value.
    VReal Scientific
  | -- | Evaluated record type.
    VRecordTy [(Name, Value)]
  | -- | An evaluated record.
    VRecord [(Name, Value)]
  | -- | Evaluated nominal inductive type.
    VAdtTy Name [Value]
  | -- | An evaluated data constructor with its argument
    -- values.
    VCnstr Name [Value]
  deriving stock (Show, Eq, Ord)

-- | De Bruijn Indices.
--
-- 'Ix' is used to reference lambda-bound terms with respect to α-conversion.
-- The index @n@ represents the value bound by the @n@th lambda counting outward
-- from the site of the index.
--
-- λ.λ.λ.2
-- ^-----^
--
-- The phantom @sort@ parameter tags which namespace the index lives in:
-- 'Value' for term indices, 'VLevel' for level indices. Keeps 'SVar'
-- (term) and 'SLVar' (level) from being silently crossed at the type
-- level.
newtype Ix sort
  = Ix Int
  deriving newtype (Show, Eq, Ord)

-- | De Bruijn Levels.
--
-- Similar to de Bruijn indices but counting inward from the outermost lambda.
--
-- λ.λ.λ.0
-- ^-----^
--
-- Levels eliminate the need to reindex free variables when weakening the
-- context. This is useful in our 'Value' representation of lambdas where we
-- have a 'Closure' holding a stack of free variables.
--
-- Like 'Ix', 'Lvl' carries a phantom @sort@ parameter distinguishing
-- term levels ('Lvl' 'Value') from level-sort levels ('Lvl' 'VLevel').
-- Arithmetic helpers like 'incLevel' and 'quoteLvl' are polymorphic in
-- the sort; constructors and binders that tie into one namespace
-- ('VVar', 'VLVar', 'bindVar', 'bindLevelVar') pin it.
newtype Lvl sort
  = Lvl Int
  deriving newtype (Show, Eq, Ord)

initLevel :: Lvl sort
initLevel = Lvl 0

incLevel :: Lvl sort -> Lvl sort
incLevel (Lvl n) = Lvl (1 + n)

newtype Name = Name {getName :: String}
  deriving newtype (Show, Eq, Ord, IsString)

-- | A neutral term is a head (a variable) applied to a spine of eliminators. We
-- can't reduce it because the head is a variable, we don't know what it is. For
-- example, @x (λy. y) ()@ is a neutral with head @x@ and spine @[VApp (λy. y),
-- VApp ()]@.
data Neutral = Neutral {head :: Head, spine :: SnocList Frame}
  deriving stock (Show, Eq, Ord)

-- | The head of a neutral term.
data Head
  = -- | A free variable at a given de Bruijn level.
    VVar (Lvl Value)
  | -- | A typed hole. Carries the expected type for
    -- round-trip quoting.
    VHole Syntax
  deriving (Show, Eq, Ord)

-- | A single eliminator in a neutral's spine.
data Frame
  = -- | Term application. Carries the argument's type and
    -- value.
    VApp Value Value
  | -- | A stuck level application. The head is a neutral at
    -- a 'VLevelPi' type and the argument is an evaluated
    -- level.
    VLevelApp VLevel
  | -- | A stuck first projection.
    VFst
  | -- | A stuck second projection.
    VSnd
  | -- | A stuck if-then-else. The condition is neutral so we
    -- can't choose a branch. Carries the motive and both
    -- branch values.
    VIf Value Value Value
  | -- | A stuck record projection.
    VGet Name
  | -- | A stuck case: the scrutinee is neutral.
    VSumCase Value Value Value Value Value
  | -- | A stuck absurd: the scrutinee is neutral at 'VoidTy'.
    VAbsurd Value
  | -- | A stuck nominal case: the scrutinee is neutral.
    VCase Value [(Name, Value)]
  deriving stock (Show, Eq, Ord)

pushFrame :: Neutral -> Frame -> Neutral
pushFrame Neutral {..} frame = Neutral {head = head, spine = Snoc spine frame}

-- | A closure pairing a body with its defining environment.
-- Captures the full 'EvalEnv' (not just term bindings)
-- because the body may reference level variables in scope.
-- Instantiated by extending the term env with a value and
-- evaluating the body.
data Closure = Closure {env :: EvalEnv, body :: Syntax}
  deriving stock (Show, Eq, Ord)

--------------------------------------------------------------------------------
-- Universe Levels

-- | A universe level. @Type n@ lives at level @n@.
data Level
  = -- | 0, 1, 2
    LNat Natural
  | -- | l, m
    LVar Name
  | -- | max l m
    LMax Level Level
  | -- | l + 1
    LSucc Level
  deriving stock (Show, Eq, Ord)

-- | Core level expression with de Bruijn indices. Produced by elaboration from
-- 'Level'.
data SLevel
  = -- | Concrete level literal.
    SLNat Natural
  | -- | Level variable by de Bruijn index.
    SLVar (Ix SLevel)
  | -- | Maximum of two levels.
    SLMax SLevel SLevel
  | -- | Successor of a level.
    SLSucc SLevel
  | -- | Omega level. Not producible by 'elaborateLevel' since surface syntax
    -- has no omega constructor, but required so 'quoteLevel' can round-trip a
    -- 'VLOmega' (the type of a level-polymorphic expression) back into syntax
    -- for display.
    SLOmega Natural
  deriving stock (Show, Eq, Ord)

-- | Evaluated level expression. Concrete levels reduce fully. Expressions
-- involving variables stay stuck.
data VLevel
  = -- | Fully reduced concrete level.
    VLNat Natural
  | -- | Stuck level variable (de Bruijn level).
    VLVar (Lvl VLevel)
  | -- | Stuck max (at least one side has a variable).
    VLMax VLevel VLevel
  | -- | Stuck succ (argument has a variable).
    VLSucc VLevel
  | -- | Omega level. @omega_0@, @omega_1@, etc. Above all finite levels.
    -- @forall l. A@ lives at @Type omega_0@.
    VLOmega Natural
  deriving stock (Show, Eq, Ord)

-- | Smart constructor for max. Reduces when both sides are concrete or omega.
-- Leaves stuck otherwise.
vlmax :: VLevel -> VLevel -> VLevel
vlmax (VLNat a) (VLNat b) = VLNat (max a b)
vlmax (VLOmega n) (VLOmega m) = VLOmega (max n m)
vlmax (VLOmega n) _ = VLOmega n
vlmax _ (VLOmega n) = VLOmega n
vlmax a b
  | a == b = a
  | otherwise = VLMax a b

-- | Smart constructor for succ. Reduces when the argument is concrete or omega.
-- Leaves stuck otherwise.
vlsucc :: VLevel -> VLevel
vlsucc (VLNat n) = VLNat (n + 1)
vlsucc (VLOmega n) = VLOmega (n + 1)
vlsucc l = VLSucc l

-- | The maximum of a list of evaluated levels. Returns @VLNat 0@ for an empty
-- list.
foldLevels :: [VLevel] -> VLevel
foldLevels = foldl' vlmax (VLNat 0)

-- | Structural subtyping on levels. Sound but incomplete. Returns @True@ only
-- when the relationship is provably true from the structure. Returns @False@
-- for anything it cannot prove, even if the relationship holds.
vlevelLeq :: VLevel -> VLevel -> Bool
vlevelLeq (VLNat a) (VLNat b) = a <= b
vlevelLeq (VLNat _) (VLOmega _) = True
vlevelLeq (VLOmega n) (VLOmega m) = n <= m
vlevelLeq (VLOmega _) (VLNat _) = False
vlevelLeq a b | a == b = True
vlevelLeq l (VLSucc r) | l == r = True
vlevelLeq (VLNat n) (VLSucc l) = vlevelLeq (VLNat n) l
vlevelLeq l (VLMax a b) = vlevelLeq l a || vlevelLeq l b
vlevelLeq (VLMax a b) r = vlevelLeq a r && vlevelLeq b r
vlevelLeq _ _ = False

-- | A bound level variable in the typechecking context.
-- Simpler than 'Cell' because level variables have no
-- type (levels are a separate sort) and their value is
-- always a fresh 'VLVar'.
data LevelCell = LevelCell
  { levelCellName :: Name,
    levelCellValue :: VLevel
  }
  deriving stock (Show, Eq, Ord)

-- | A closure that binds a level variable. When
-- instantiated, it extends the level environment
-- instead of the term environment.
data LevelClosure = LevelClosure EvalEnv Syntax
  deriving stock (Show, Eq, Ord)

--------------------------------------------------------------------------------
-- ADTs

-- | A complete data type definition: a type name and its constructors.
--
-- For example, @DataTypeSpec "ListBool" [Constr "Nil" [], Constr "Cons" [Term
-- BoolTy, Rec]]@. Currently monomorphic. With polymorphism, this would carry
-- type parameters.
data DataTypeSpec
  = DataTypeSpec Name Int [DataConstructorSpec]
  deriving stock (Show, Eq, Ord)

-- | A single data constructor: a name and a list of argument specs. For
-- example, @Constr "Cons" [Term BoolTy, Rec]@ is the @Cons@ constructor taking
-- a @Bool@ and a recursive list.
data DataConstructorSpec
  = Constr Name [ArgSpec]
  deriving stock (Show, Eq, Ord)

getCnstrName :: DataConstructorSpec -> Name
getCnstrName (Constr nm _) = nm

-- | Specifies the type of a single constructor argument. 'Term' means a
-- concrete type, 'Rec' means a recursive reference to the enclosing data type.
data ArgSpec
  = Term Syntax
  | -- | A recursive reference to the enclosing data type.
    Rec
  | TyParam Int
  deriving stock (Show, Eq, Ord)

-- | We predefine a few ADTs here for demonstration purposes. In a complete
-- language these would be defined using 'data' declarations in a module.
stockADTs :: Map Name DataTypeSpec
stockADTs =
  Map.fromList
    [ ("Maybe", DataTypeSpec "Maybe" 1 [Constr "Nothing" [], Constr "Just" [TyParam 0]]),
      ("List", DataTypeSpec "List" 1 [Constr "Nil" [], Constr "Cons" [TyParam 0, Rec]])
    ]

--------------------------------------------------------------------------------
-- Environment
--
-- The typechecker's context. Elaboration needs to track names (for resolving
-- named variables), types (for typechecking), and values (for quoting back from
-- the semantic domain). A 'Cell' bundles all three for each binding.

-- | A single binding in the context: a name, its type, and its value. The value
-- is a fresh neutral for lambda-bound variables (we don't know what they'll be
-- applied to) or an actual value for let-bound variables.
data Cell = Cell
  { cellName :: Name,
    cellType :: Value,
    cellValue :: Value
  }
  deriving stock (Show, Eq, Ord)

-- | The typechecker/elaboration context.
--
-- @localValues@ holds values by de Bruijn index, @localValuesNames@ maps names
-- to 'Cell's for resolution, and @localValuesSize@ tracks the current binding
-- depth. Type and term variables share a single index space.
data TypeCheckEnv = TypeCheckEnv
  { localValues :: SnocList Value,
    localValuesNames :: [Cell],
    localValuesSize :: Int,
    localLevels :: SnocList VLevel,
    localLevelsNames :: [LevelCell],
    localLevelsSize :: Int,
    -- | Holes encountered during typechecking
    holes :: [Syntax],
    -- | ADT Spec by Constructor Name
    adtConstructors :: Map Name DataTypeSpec
  }
  deriving stock (Show, Eq, Ord)

-- | The evaluator's environment. A snoc list of variable bindings
-- and the current depth. Used as the top-level eval environment
-- and projected from the typechecker context.
data EvalEnv = EvalEnv
  { -- | Variable bindings, indexed by de Bruijn index.
    envValues :: SnocList Value,
    -- | Current term binding depth.
    envValuesLen :: Int,
    -- | Level variable bindings, indexed by level de
    -- Bruijn index. Separate from term bindings.
    envLevels :: SnocList VLevel,
    -- | Current level binding depth.
    envLevelsLen :: Int,
    -- | ADT Spec by Constructor Name
    envAdtConstructors :: Map Name DataTypeSpec
  }
  deriving stock (Show, Eq, Ord)

-- | Project the evaluator environment from the typechecker context. The
-- typechecker carries extra metadata (names, holes, ADT specs) that the
-- evaluator does not need.
toEvalEnv :: TypeCheckEnv -> EvalEnv
toEvalEnv env =
  EvalEnv
    { envValues = env.localValues,
      envValuesLen = env.localValuesSize,
      envLevels = env.localLevels,
      envLevelsLen = env.localLevelsSize,
      envAdtConstructors = env.adtConstructors
    }

adtConstructorsMap :: Map Name DataTypeSpec
adtConstructorsMap = Map.fromList $ foldr (\d@(DataTypeSpec _ _ cs) acc -> fmap ((,d) . getCnstrName) cs <> acc) [] stockADTs

-- | Lookup a Data Constructor Spec from a Data Constructor Name.
lookupDataCnstrSpec :: Name -> (DataConstructorSpec -> TypecheckM a) -> TypecheckM a
lookupDataCnstrSpec nm k =
  lookupDataTypeSpec nm $ \(DataTypeSpec tyName _ specs) ->
    case find (\(Constr nm' _) -> nm == nm') specs of
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
  case find (\(DataTypeSpec tyName' _ _) -> tyName == tyName') cnstrs of
    Just dataSpec -> k dataSpec
    Nothing -> throwError $ OutOfScopeError tyName

initEnv :: TypeCheckEnv
initEnv = TypeCheckEnv Nil [] 0 Nil [] 0 mempty adtConstructorsMap

extendLocalNames :: TypeCheckEnv -> Cell -> TypeCheckEnv
extendLocalNames e@TypeCheckEnv {localValuesNames} cell = e {localValuesNames = cell : localValuesNames}

extendHoles :: Syntax -> TypeCheckEnv -> TypeCheckEnv
extendHoles ty e@TypeCheckEnv {holes} = e {holes = ty : holes}

bindCell :: Cell -> TypeCheckEnv -> TypeCheckEnv
bindCell cell@Cell {..} TypeCheckEnv {..} =
  TypeCheckEnv
    { localValues = Snoc localValues cellValue,
      localValuesNames = cell : localValuesNames,
      localValuesSize = localValuesSize + 1,
      localLevels = localLevels,
      localLevelsNames = localLevelsNames,
      localLevelsSize = localLevelsSize,
      holes = holes,
      adtConstructors = adtConstructors
    }

bindLevelCell :: LevelCell -> TypeCheckEnv -> TypeCheckEnv
bindLevelCell cell@LevelCell {..} TypeCheckEnv {..} =
  TypeCheckEnv
    { localValues = localValues,
      localValuesNames = localValuesNames,
      localValuesSize = localValuesSize,
      localLevels = Snoc localLevels levelCellValue,
      localLevelsNames = cell : localLevelsNames,
      localLevelsSize = localLevelsSize + 1,
      holes = holes,
      adtConstructors = adtConstructors
    }

resolveCell :: TypeCheckEnv -> Name -> Maybe Cell
resolveCell TypeCheckEnv {..} bndr = find ((== bndr) . cellName) localValuesNames

-- | Create a fresh neutral variable at the current depth. Used for lambda-bound
-- variables where we don't know the value.
freshVar :: TypeCheckEnv -> Value -> Value
freshVar TypeCheckEnv {localValuesSize} ty = VNeutral ty $ Neutral (VVar $ Lvl localValuesSize) Nil

freshLevelVar :: TypeCheckEnv -> VLevel
freshLevelVar TypeCheckEnv {localLevelsSize} = VLVar (Lvl localLevelsSize)

-- | Create a fresh cell for a lambda-bound variable. The value is a neutral
-- because we don't know the argument yet.
freshCell :: TypeCheckEnv -> Name -> Value -> Cell
freshCell ctx name ty = Cell name ty (freshVar ctx ty)

freshLevelCell :: TypeCheckEnv -> Name -> LevelCell
freshLevelCell ctx name = LevelCell name (freshLevelVar ctx)

--------------------------------------------------------------------------------
-- Typechecker
--
-- The typechecker is split into two mutually recursive judgements:
--
--   - 'Synth': The term tells us its type.
--   - 'Check': We push an expected type into the term.
--
-- Terms that introduce a type former (lambdas, pairs, unit) are checked. Terms
-- that eliminate one (application, projection) or carry an annotation are
-- synthesized. The 'subTactic' bridges the two directions.
--
-- Each tactic returns the elaborated core IR: 'Check' returns @Type ->
-- TypecheckM Syntax@ and 'Synth' returns @TypecheckM (Type, Syntax)@. This is
-- the "elaboration." Typechecking and translation happen in one pass.

data Error
  = TypeError String
  | OutOfScopeError Name
  deriving (Show)

-- | Accumulated hole types from typechecking. Each time the typechecker
-- encounters a 'Hole' in check position, it 'tell's the expected type here.
newtype Holes = Holes {getHoles :: [Syntax]}
  deriving newtype (Show, Semigroup, Monoid)

newtype TypecheckM a = TypecheckM {runTypecheckM :: TypeCheckEnv -> (Either Error a, Holes)}
  deriving
    (Functor, Applicative, Monad, MonadReader TypeCheckEnv, MonadError Error, MonadWriter Holes)
    via (ExceptT Error (WriterT Holes (Reader TypeCheckEnv)))

newtype Check = Check {runCheck :: Value -> TypecheckM Syntax}

newtype Synth = Synth {runSynth :: TypecheckM (Value, Syntax)}

synth :: Term -> Synth
synth = \case
  -- Core
  Var bndr -> varTactic bndr
  Ap tm1 tm2 -> piElim (synth tm1) (check tm2)
  Anno ty tm -> annoTactic ty (check tm)
  Hole -> Synth $ throwError $ TypeError "Cannot synthesize holes"
  -- Universe
  Univ l -> Synth $ do
    sl <- elaborateLevel l
    runSynth $ univFormation sl
  -- Pi / Function
  FuncTy a b -> funcTyFormationSynth (synth a) (synth b)
  Pi nm a b -> piFormationSynth nm (synth a) (synth b)
  LevelPi nm body -> levelPiFormation nm (synth body)
  LevelAp f l -> levelApElim (synth f) l
  -- Sigma / Pair
  Sigma nm a b -> sigmaFormationSynth nm (synth a) (synth b)
  PairTy a b -> pairTyFormationSynth (synth a) (synth b)
  Fst tm -> sigmaElimFst (synth tm)
  Snd tm -> sigmaElimSnd (synth tm)
  -- Bool
  BoolTy -> boolFormation
  If tm1 tm2 tm3 -> boolElimSynth (check tm1) (synth tm2) (synth tm3)
  -- Unit
  UnitTy -> unitFormation
  -- Void
  VoidTy -> voidFormation
  -- Sum
  SumTy a b -> sumFormationSynth (synth a) (synth b)
  -- Numerics
  NaturalTy -> natFormation
  IntegerTy -> intFormation
  RealTy -> realFormation
  -- Records
  RecordTy fields -> recordFormationSynth (fmap (fmap synth) fields)
  Get name tm -> recordElim name (synth tm)
  -- ADTs
  AdtTy nm tys -> adtFormationSynth nm (fmap synth tys)
  -- Catch-all
  tm -> Synth $ throwError $ TypeError $ "Cannot synthesize type for " <> show tm

elaborateLevel :: Level -> TypecheckM SLevel
elaborateLevel (LNat n) = pure (SLNat n)
elaborateLevel (LVar nm) = do
  ctx <- ask
  case resolveLevelCell ctx nm of
    Just cell -> do
      let ix =
            quoteLvl
              (Lvl ctx.localLevelsSize)
              (lvlOfVLevel cell.levelCellValue)
      pure (SLVar ix)
    Nothing ->
      throwError $ OutOfScopeError nm
elaborateLevel (LMax a b) =
  SLMax <$> elaborateLevel a <*> elaborateLevel b
elaborateLevel (LSucc a) =
  SLSucc <$> elaborateLevel a

resolveLevelCell :: TypeCheckEnv -> Name -> Maybe LevelCell
resolveLevelCell TypeCheckEnv {..} nm =
  find ((== nm) . levelCellName) localLevelsNames

lvlOfVLevel :: VLevel -> Lvl VLevel
lvlOfVLevel (VLVar lvl) = lvl
lvlOfVLevel _ = error "impossible: level cell is not a variable"

check :: Term -> Check
check = \case
  -- Core
  Lam bndr body -> piIntro bndr (check body)
  Let bndr e body -> letTactic bndr (synth e) (check body)
  Hole -> holeTactic
  -- Pi / Function
  FuncTy a b -> funcTyFormationCheck (check a) (check b)
  Pi nm a b -> piFormationCheck nm (check a) (check b)
  LevelLam bndr body -> levelLamIntro bndr (check body)
  -- Sigma / Pair
  Sigma nm a b -> sigmaFormationCheck nm (check a) (check b)
  PairTy a b -> pairTyFormationCheck (check a) (check b)
  Pair tm1 tm2 -> sigmaIntro (check tm1) (check tm2)
  -- Bool
  Tru -> boolIntroTrue
  Fls -> boolIntroFalse
  If tm1 tm2 tm3 -> boolElimCheck (check tm1) (check tm2) (check tm3)
  -- Unit
  Unit -> unitIntro
  -- Void
  Absurd tm -> voidElim (synth tm)
  -- Sum
  SumTy a b -> sumFormationCheck (check a) (check b)
  InL tm1 -> sumIntroL (check tm1)
  InR tm2 -> sumIntroR (check tm2)
  SumCase scrut (bndr1, t1) (bndr2, t2) -> sumElim (synth scrut) (check (Lam bndr1 t1)) (check (Lam bndr2 t2))
  -- Numerics
  Natural n -> natIntro n
  Integer z -> intIntro z
  Real r -> realIntro r
  -- Records
  RecordTy fields -> recordFormationCheck (fmap (fmap check) fields)
  Record fields -> recordIntro (fmap (fmap (id &&& check)) fields)
  -- ADTs
  AdtTy nm tys -> adtFormationCheck nm (fmap check tys)
  Cnstr nm args -> adtIntro nm (fmap check args)
  Case scrut cases -> adtElim (synth scrut) (fmap (\(x, y, z) -> (x, check (foldr Lam z y))) cases)
  -- Catch-all: switch to synth mode
  tm -> subTactic (synth tm)

-- | Extract the universe level from a value. Throws a
-- type error if the value is not a universe.
expectUniv :: Value -> TypecheckM VLevel
expectUniv (VUniv n) = pure n
expectUniv ty =
  throwError $
    TypeError $
      "Expected a Type, but got: " <> show ty

-- | Quote a 'Value' back to 'Syntax' from 'TypecheckM'. Projects
-- the eval env and current level from the typechecker context.
quoteValue :: Value -> Value -> TypecheckM Syntax
quoteValue ty val = do
  ctx <- ask
  let l = Lvl ctx.localValuesSize
      vl = Lvl ctx.localLevelsSize
  pure $ runEvalM (quote l vl ty val) (toEvalEnv ctx)

-- | Var Tactic
--
-- Resolve a named variable to its type and elaborated form. This is where name
-- resolution happens.
--
-- we look up the name in 'localNames' to get the 'Cell', then quote the cell's
-- value back to 'Syntax' to produce the elaborated output.
--
-- The quoting step is what converts the de Bruijn level in the cell's value to
-- a de Bruijn index in the syntax.
--
-- (x : A) ∈ Γ
-- ─────────── Var⇒
--  Γ ⊢ x ⇒ A
varTactic :: Name -> Synth
varTactic bndr = Synth $ do
  ctx <- ask

  case resolveCell ctx bndr of
    Just Cell {..} -> do
      let quoted = flip runEvalM (toEvalEnv ctx) $ quote (Lvl ctx.localValuesSize) (Lvl ctx.localLevelsSize) cellType cellValue
      pure (cellType, quoted)
    Nothing -> throwError $ OutOfScopeError bndr

-- | Sub Tactic
--
-- The bridge between synth and check. Synthesize a type for the term, then
-- verify it is a subtype of the expected type. This replaces the equality check
-- from earlier modules. This is how a synthesizable term (like a variable or
-- annotation) can appear in a checked position. Every term that doesn't have
-- its own check rule falls through to this.
--
-- Γ ⊢ e ⇒ A  A <∶ B
-- ──────────────── Sub⇐
--    Γ ⊢ e ⇐ B
-- | Run 'isSubtypeOf' from 'TypecheckM'. Projects the eval env
-- and current level from the typechecker context.
checkSubtype :: Value -> Value -> TypecheckM Bool
checkSubtype sub super = do
  ctx <- ask
  let l = Lvl ctx.localValuesSize
  pure $ runEvalM (isSubtypeOf l sub super) (toEvalEnv ctx)

subTactic :: Synth -> Check
subTactic (Synth synth) = Check $ \ty1 -> do
  (ty2, tm) <- synth
  ok <- checkSubtype ty2 ty1
  if ok
    then pure tm
    else throwError $ TypeError $ "Type '" <> show ty2 <> "' cannot be a subtype of type '" <> show ty1 <> "'"

-- | Anno Tactic
--
-- The annotation provides a type, switching from synth to check mode. We check
-- the body against the annotated type, then synthesize that type as the result.
-- The annotation itself is erased during elaboration, it doesn't appear in the
-- core 'Syntax'.
--
--  Γ ⊢ A ⇒ Type k    Γ ⊢ e ⇐ A
--  ─────────────────────────────── Anno⇒
--       Γ ⊢ (e : A) ⇒ A
annoTactic :: Term -> Check -> Synth
annoTactic ty (Check bodyTac) = Synth $ do
  (_, sty) <- runSynth (synth ty)
  vty <- asks $ runEvalM (eval sty) . toEvalEnv
  body <- bodyTac vty

  pure (vty, body)

-- | Pi Introduction
--
-- A lambda is checked against a function type. The expected type @A₁ → A₂@
-- tells us what type the parameter has (@A₁@), so we extend the context and
-- check the body against the return type (@A₂@). This is why lambdas can't
-- synthesize. Without the expected function type, we wouldn't know @A₁@.
--
-- Elaborates to @SLam name body'@.
--
--  Γ, x : A₁ ⊢ e ⇐ A₂
-- ──────────────────── LamIntro⇐
-- Γ ⊢ (λx.e) ⇐ A₁ → A₂
piIntro :: Name -> Check -> Check
piIntro bndr (Check bodyTac) = Check $ \case
  VFuncTy a b -> do
    ctx <- ask
    let var = freshCell ctx bndr a
    fiber <- local (bindCell var) $ bodyTac b
    pure $ SLam bndr fiber
  VPi _ a clo -> do
    var <- asks $ \ctx -> freshCell ctx bndr a
    fiber <- local (bindCell var) $ do
      ctx <- asks toEvalEnv
      let b = runEvalM (appClosure clo var.cellValue) ctx
      bodyTac b
    pure $ SLam bndr fiber
  ty -> throwError $ TypeError $ "Tried to introduce a lambda at a non-function type: " <> show ty

-- | Level Lambda Introduction
--
-- Check a level abstraction against a level-Pi type. Binds the
-- parameter to a fresh level variable, instantiates the body-type
-- closure at that variable to get the expected type of the body, then
-- checks the body there. Elaborates to @SLevelLam bndr body'@.
--
--  Γ, l : Level ⊢ e ⇐ A
-- ─────────────────────── LevelLam⇐
--   Γ ⊢ (Λl. e) ⇐ ∀l. A
levelLamIntro :: Name -> Check -> Check
levelLamIntro bndr (Check tac) = Check $ \case
  VLevelPi _ clo -> do
    var <- asks $ \ctx -> freshLevelCell ctx bndr
    fiber <- local (bindLevelCell var) $ do
      ctx <- asks toEvalEnv
      let b = runEvalM (appLevelClosure clo var.levelCellValue) ctx
      tac b
    pure $ SLevelLam bndr fiber
  ty -> throwError $ TypeError $ "Tried to introduce a level lambda at a non-level-Pi type: " <> show ty

-- | Pi Elimination
--
-- Application is a synth rule. Synthesize the function's type to get @A → B@,
-- then check the argument against @A@, and return @B@. The function type tells
-- us what to check the argument against. Information flows from the function to
-- the argument.
--
-- Elaborates to @SAp f' arg'@.
--
-- Γ ⊢ e₁ ⇒ A → B  Γ ⊢ e₂ ⇐ A
-- ────────────────────────── LamElim⇒
--       Γ ⊢ e₁ e₂ ⇒ B
piElim :: Synth -> Check -> Synth
piElim (Synth funcTac) (Check argTac) =
  Synth $
    funcTac >>= \case
      (a `VFuncTy` b, f) -> do
        arg <- argTac a
        pure (b, SAp f arg)
      (VPi _ a clo, f) -> do
        arg <- argTac a
        ctx <- asks toEvalEnv
        let vArg = runEvalM (eval arg) ctx
            b = runEvalM (appClosure clo vArg) ctx
        pure (b, SAp f arg)
      (ty, _) -> throwError $ TypeError $ "Expected a function type but got " <> show ty

-- | Level Application
--
-- Level application is a synth rule. Synthesize the function's type
-- to get @∀l. A@, elaborate and evaluate the surface level argument,
-- then instantiate the closure at that level to compute the result
-- type. Elaborates to @SLevelAp f' sl@.
--
--  Γ ⊢ e ⇒ ∀l. A
-- ───────────────────── LevelAp⇒
-- Γ ⊢ e \@L ⇒ A[l := L]
levelApElim :: Synth -> Level -> Synth
levelApElim (Synth tac) l =
  Synth $
    tac >>= \case
      (VLevelPi _ clo, f) -> do
        ctx <- asks toEvalEnv
        sl <- elaborateLevel l
        let vl = runEvalM (evalLevel sl) ctx
            body = runEvalM (appLevelClosure clo vl) ctx
        pure (body, SLevelAp f sl)
      (ty, _) -> throwError $ TypeError $ "Expected a level-polymorphic function but got: " <> show ty

-- | Let Tactic
--
-- @let x = e in body@ elaborates to @(λx. body') e'@. There is no dedicated
-- @SLet@ in the core syntax. The let is fully dissolved by NbE: the beta redex
-- reduces and the bound value is inlined into the normal form.
--
-- Unlike 'piIntro', which binds a fresh neutral variable (since the argument
-- is unknown), the let tactic evaluates @e@ and stores the resulting value in
-- the context cell. This means references to @x@ in the body see the actual
-- value during elaboration, not a stuck variable.
--
--  Γ ⊢ e ⇒ A    Γ, x : A ⊢ body ⇐ B
--  ──────────────────────────────────── Let⇐
--        Γ ⊢ let x = e in body ⇐ B
letTactic :: Name -> Synth -> Check -> Check
letTactic bndr (Synth synth) (Check bodyTac) = Check $ \ty -> do
  (ty1, tm1) <- synth
  ctx <- asks toEvalEnv
  let val = runEvalM (eval tm1) ctx
      var = Cell bndr ty1 val
  fiber <- local (bindCell var) $ bodyTac ty
  pure $ SAp (SLam bndr fiber) tm1

-- | Type Hole Tactic
--
-- A hole accepts any expected type and records it via the 'Writer' effect.
-- Elaborates to @SHole ty@, which evaluates to a neutral and survives through
-- NbE.
--
-- The normal form still shows the hole with its type. Holes can only appear in
-- check position; in synth position there's no expected type to record, so it's
-- an error.
--
-- ────────── Hole⇐
--  Γ ⊢ ? ⇐ A
holeTactic :: Check
holeTactic = Check $ \ty -> do
  ty <- quoteValue (VUniv (VLNat 0)) ty
  tell (Holes [ty])
  pure (SHole ty)

-- | Universe Formation
--
-- @Type n : Type (n + 1)@.
--
--  ─────────────────────────── Univ⇒
--  Γ ⊢ Type n ⇒ Type (n + 1)
univFormation :: SLevel -> Synth
univFormation sl = Synth $ do
  vl <- asks $ runEvalM (evalLevel sl) . toEvalEnv
  pure (VUniv (vlsucc vl), SUniv sl)

-- | Pi Formation Rule Synth
--
--  Γ ⊢ A ⇒ Type n    Γ, x : A ⊢ B ⇒ Type m
--  ─────────────────────────────────────────── Pi⇒
--       Γ ⊢ (x : A) → B ⇒ Type (max n m)
piFormationSynth :: Name -> Synth -> Synth -> Synth
piFormationSynth nm (Synth domSynth) (Synth codSynth) = Synth $ do
  (domTy, sa) <- domSynth
  n <- expectUniv domTy
  ctx <- ask
  let va = runEvalM (eval sa) (toEvalEnv ctx)
      var = freshCell ctx nm va
  (codTy, sb) <- local (bindCell var) codSynth
  m <- expectUniv codTy
  pure (VUniv (vlmax n m), SPi nm sa sb)

-- | Pi Formation Check
--
-- Dependent function type. The domain and codomain are both checked against the
-- goal universe level. Cumulativity ensures this accepts components at any
-- lower level. Elaborates to @SPi nm sa sb@.
--
--  Γ ⊢ A ⇐ Type k    Γ, x : A ⊢ B ⇐ Type k
--  ─────────────────────────────────────── Pi⇐
--       Γ ⊢ (x : A) → B ⇐ Type k
piFormationCheck :: Name -> Check -> Check -> Check
piFormationCheck nm (Check domTac) (Check codTac) = Check $ \case
  VUniv k -> do
    sa <- domTac (VUniv k)
    ctx <- ask
    let va = runEvalM (eval sa) (toEvalEnv ctx)
        var = freshCell ctx nm va
    sb <- local (bindCell var) $ codTac (VUniv k)
    pure (SPi nm sa sb)
  ty ->
    throwError $
      TypeError $
        "Expected a Type, but got: " <> show ty

-- | Function Type Formation Synth
--
-- Non-dependent function type. Synthesizes both components, extracts their
-- universe levels, and returns the maximum. Elaborates to @SFuncTy sa sb@.
--
--  Γ ⊢ A ⇒ Type n    Γ ⊢ B ⇒ Type m
--  ─────────────────────────────────── Arrow⇒
--       Γ ⊢ A → B ⇒ Type (max n m)
funcTyFormationSynth :: Synth -> Synth -> Synth
funcTyFormationSynth (Synth domTac) (Synth codTac) = Synth $ do
  (domTy, sa) <- domTac
  n <- expectUniv domTy
  (codTy, sb) <- codTac
  m <- expectUniv codTy
  pure (VUniv (vlmax n m), SFuncTy sa sb)

-- | Function Type Formation Check
--
-- Non-dependent function type. The domain and codomain are both checked against
-- the goal universe level. Cumulativity ensures this accepts components at any
-- lower level. Elaborates to @SFuncTy sa sb@.
--
--  Γ ⊢ A ⇐ Type k    Γ ⊢ B ⇐ Type k
--  ─────────────────────────────────── Arrow⇐
--       Γ ⊢ A → B ⇐ Type k
funcTyFormationCheck :: Check -> Check -> Check
funcTyFormationCheck (Check domTac) (Check codTac) = Check $ \case
  VUniv k -> do
    sa <- domTac (VUniv k)
    sb <- codTac (VUniv k)

    pure (SFuncTy sa sb)
  ty ->
    throwError $
      TypeError $
        "Expected a Type, but got: " <> show ty

-- | Level Pi Formation
--
-- Quantification over levels always lives at @Type ω₀@, a special
-- level above all finite levels. This pushes level-polymorphic
-- definitions out of the finite hierarchy into the omega hierarchy,
-- avoiding the circularity of @Type : Type@. The synthesized level of
-- the body is discarded since the result is always @Type ω₀@.
-- Elaborates to @SLevelPi nm sb@.
--
--  Γ, l : Level ⊢ A ⇒ Type k
-- ─────────────────────────── LevelPi⇒
--      Γ ⊢ (∀l. A) ⇒ Type ω₀
levelPiFormation :: Name -> Synth -> Synth
levelPiFormation bndr (Synth tac) = Synth $ do
  var <- asks $ \ctx -> freshLevelCell ctx bndr
  local (bindLevelCell var) $ do
    (ty, body) <- tac
    _ <- expectUniv ty
    pure (VUniv (VLOmega 0), SLevelPi bndr body)

-- | Sigma Formation Synth
--
-- Dependent pair type. Synthesizes both components, extracts their universe
-- levels, and returns the maximum. A fresh variable of the first component's
-- type is bound so the second component can reference it. Elaborates to @SSigma
-- nm sa sb@.
--
--  Γ ⊢ A ⇒ Type n    Γ, x : A ⊢ B ⇒ Type m
--  ─────────────────────────────────────────── Sigma⇒
--       Γ ⊢ (x : A) × B ⇒ Type (max n m)
sigmaFormationSynth :: Name -> Synth -> Synth -> Synth
sigmaFormationSynth nm (Synth domTac) (Synth codTac) = Synth $ do
  (domTy, sa) <- domTac
  n <- expectUniv domTy
  ctx <- ask
  let va = runEvalM (eval sa) (toEvalEnv ctx)
      var = freshCell ctx nm va
  (codTy, sb) <- local (bindCell var) codTac
  m <- expectUniv codTy

  pure (VUniv (vlmax n m), SSigma nm sa sb)

-- | Sigma Formation Check
--
-- Dependent pair type. The first and second component types are both checked
-- against the goal universe level. A fresh variable of the first component's
-- type is bound so the second component can reference it. Cumulativity ensures
-- this accepts components at any lower level. Elaborates to @SSigma nm sa sb@.
--
--  Γ ⊢ A ⇐ Type k    Γ, x : A ⊢ B ⇐ Type k
--  ─────────────────────────────────────── Sigma⇐
--       Γ ⊢ (x : A) × B ⇐ Type k
sigmaFormationCheck :: Name -> Check -> Check -> Check
sigmaFormationCheck nm (Check domTac) (Check codTac) = Check $ \case
  VUniv k -> do
    sa <- domTac (VUniv k)
    ctx <- ask
    let va = runEvalM (eval sa) (toEvalEnv ctx)
        var = freshCell ctx nm va
    sb <- local (bindCell var) $ codTac (VUniv k)

    pure (SSigma nm sa sb)
  ty ->
    throwError $
      TypeError $
        "Expected a Type, but got: " <> show ty

-- | Pair Type Formation Synth
--
-- Non-dependent pair type. Synthesizes both components, extracts their universe
-- levels, and returns the maximum. Elaborates to @SPairTy sa sb@.
--
--  Γ ⊢ A ⇒ Type n    Γ ⊢ B ⇒ Type m
--  ─────────────────────────────────── Pair⇒
--       Γ ⊢ A × B ⇒ Type (max n m)
pairTyFormationSynth :: Synth -> Synth -> Synth
pairTyFormationSynth (Synth fstTac) (Synth sndTac) = Synth $ do
  (fstTy, sa) <- fstTac
  n <- expectUniv fstTy

  (sndTy, sb) <- sndTac
  m <- expectUniv sndTy

  pure (VUniv (vlmax n m), SPairTy sa sb)

-- | Pair Type Formation Check
--
-- Non-dependent pair type. Both components are checked against the goal
-- universe level. Cumulativity ensures this accepts components at any lower
-- level. Elaborates to @SPairTy sa sb@.
--
--  Γ ⊢ A ⇐ Type k    Γ ⊢ B ⇐ Type k
--  ─────────────────────────────────── Pair⇐
--       Γ ⊢ A × B ⇐ Type k
pairTyFormationCheck :: Check -> Check -> Check
pairTyFormationCheck (Check fstTac) (Check sndTac) = Check $ \case
  VUniv k -> do
    sa <- fstTac (VUniv k)
    sb <- sndTac (VUniv k)

    pure (SPairTy sa sb)
  ty ->
    throwError $
      TypeError $
        "Expected a Type, but got: " <> show ty

-- | Sigma Introduction
--
-- Like lambdas, pairs are checked. the expected pair type @A × B@ tells us what
-- to check each component against.
--
-- Elaborates to @SPair a' b'@.
--
-- Γ ⊢ a ⇐ A   Γ ⊢ b ⇐ B
-- ───────────────────── Pair⇐
--  Γ ⊢ (a , b) ⇐ A × B
sigmaIntro :: Check -> Check -> Check
sigmaIntro (Check checkFst) (Check checkSnd) = Check $ \case
  VSigma _ a clo -> do
    tm1 <- checkFst a
    ctx <- asks toEvalEnv
    let v1 = runEvalM (eval tm1) ctx
        b = runEvalM (appClosure clo v1) ctx
    tm2 <- checkSnd b

    pure (SPair tm1 tm2)
  VPairTy a b -> do
    tm1 <- checkFst a
    tm2 <- checkSnd b
    pure (SPair tm1 tm2)
  ty -> throwError $ TypeError $ "Couldn't match expected type Pair with actual type '" <> show ty <> "'"

-- | Sigma Fst Elimination
--
-- Projection is a synth rule. Synthesize the pair's type to learn what the
-- components are, then return the appropriate one.
--
-- Γ ⊢ (t₁ , t₂) ⇒ A × B
-- ───────────────────── Fst⇒
--       Γ ⊢ t₁ ⇒ A
sigmaElimFst :: Synth -> Synth
sigmaElimFst (Synth synth) =
  Synth $
    synth >>= \case
      (VPairTy ty1 _ty2, tm) -> pure (ty1, SFst tm)
      (VSigma _ a _clo, tm) -> pure (a, SFst tm)
      (ty, _) -> throwError $ TypeError $ "Couldn't match expected type Pair with actual type '" <> show ty <> "'"

-- | Sigma Snd Elimination
--
-- Same as fst, but returns the second component.
--
-- Γ ⊢ (t₁ , t₂) ⇒ A × B
-- ───────────────────── Snd⇒
--       Γ ⊢ t₂ ⇒ B
sigmaElimSnd :: Synth -> Synth
sigmaElimSnd (Synth synth) =
  Synth $
    synth >>= \case
      (VPairTy _ty1 ty2, tm) -> pure (ty2, SSnd tm)
      (VSigma _ _a clo, tm) -> do
        ctx <- asks toEvalEnv
        let vpair = runEvalM (eval tm) ctx
            v1 = runEvalM (doFst vpair) ctx
            b = runEvalM (appClosure clo v1) ctx
        pure (b, SSnd tm)
      (ty, _) -> throwError $ TypeError $ "Couldn't match expected type Pair with actual type '" <> show ty <> "'"

-- | Bool Formation
--
-- ────────────────── Bool⇒
-- Γ ⊢ Bool ⇒ Type 0
boolFormation :: Synth
boolFormation = Synth $ pure (VUniv (VLNat 0), SBoolTy)

-- | Bool True Introduction
--
-- Checked against 'BoolTy' (or a supertype via subtyping).
--
-- ──────────────── True⇐
-- Γ ⊢ True ⇐ Bool
boolIntroTrue :: Check
boolIntroTrue = Check $ \case
  VBoolTy -> pure STru
  ty -> do
    ok <- checkSubtype VBoolTy ty
    if ok
      then pure STru
      else throwError $ TypeError $ "'Bool' cannot be a subtype of '" <> show ty <> "'"

-- | Bool False Introduction
--
-- Checked against 'BoolTy'. Elaborates to 'SFls' (or a supertype via subtyping).
--
-- ──────────────── False⇐
-- Γ ⊢ False ⇐ Bool
boolIntroFalse :: Check
boolIntroFalse = Check $ \case
  VBoolTy -> pure SFls
  ty -> do
    ok <- checkSubtype VBoolTy ty
    if ok
      then pure SFls
      else throwError $ TypeError $ "'Bool' cannot be a subtype of '" <> show ty <> "'"

-- | Bool Elimination Check
--
-- Check the condition against 'BoolTy', and both branches against the expected
-- (motive) type. The motive is whatever type the @if@ expression is being
-- checked at. Elaborates to @SIf scrut' t' f'@.
--
-- Γ ⊢ t₁ ⇐ Bool  Γ ⊢ t₂ ⇐ T  Γ ⊢ t₃ ⇐ T
-- ───────────────────────────────────── If⇐
--   Γ ⊢ If t₁ then t₂ else t₃ ⇐ T
boolElimCheck :: Check -> Check -> Check -> Check
boolElimCheck (Check checkT1) (Check checkT2) (Check checkT3) = Check $ \ty -> do
  tm1 <- checkT1 VBoolTy
  tm2 <- checkT2 ty
  tm3 <- checkT3 ty
  ty <- quoteValue (VUniv (VLNat 0)) ty
  pure (SIf tm1 ty tm2 tm3)

-- | Bool Elimination Synth
--
-- Synthesizes the type of an if-expression by synthesizing both branches and
-- checking they have the same type. The condition is checked against @Bool@.
-- Unlike the Check variant, no motive is pushed down. The motive is computed
-- bottom-up from the branches. Elaborates to @SIf scrut motive sa sb@.
--
--  Γ ⊢ c ⇐ Bool    Γ ⊢ t ⇒ A    Γ ⊢ f ⇒ A
--  ──────────────────────────────────────────── If⇒
--       Γ ⊢ if c then t else f ⇒ A
boolElimSynth :: Check -> Synth -> Synth -> Synth
boolElimSynth (Check scruTac) (Synth aTac) (Synth bTac) = Synth $ do
  scrut <- scruTac VBoolTy
  (aTy, sa) <- aTac
  (bTy, sb) <- bTac

  ctx <- ask
  let l = Lvl ctx.localValuesSize
      ok = runEvalM (equateValue l aTy bTy) (toEvalEnv ctx)

  case ok of
    True -> do
      motive <- quoteValue (VUniv (VLNat 0)) aTy
      pure (aTy, SIf scrut motive sa sb)
    False ->
      throwError $ TypeError $ "If branches have different types: " <> show aTy <> " vs " <> show bTy

-- | Unit Formation
--
-- ────────────────── Unit⇒
-- Γ ⊢ Unit ⇒ Type 0
unitFormation :: Synth
unitFormation = Synth $ pure (VUniv (VLNat 0), SUnitTy)

-- | Unit Introduction
--
-- Verify the expected type is 'UnitTy' (or a supertype).
--
-- ───────────── Unit⇐
-- Γ ⊢ () ⇐ Unit
unitIntro :: Check
unitIntro = Check $ \case
  VUnitTy -> pure SUnit
  ty -> do
    ok <- checkSubtype VUnitTy ty
    if ok
      then pure SUnit
      else throwError $ TypeError $ "'Unit' cannot be a subtype of '" <> show ty <> "'"

-- | Void Formation
--
-- ────────────────── Void⇒
-- Γ ⊢ Void ⇒ Type 0
voidFormation :: Synth
voidFormation = Synth $ pure (VUniv (VLNat 0), SVoidTy)

-- | Void Elimination
--
-- Synthesize the scrutinee and verify it has type 'VoidTy'. Since no value of
-- type 'Void' exists, this branch is unreachable, but it can produce any type
-- @C@.
--
--  Γ ⊢ e ⇒ Void
--  ─────────────── Absurd⇐
--  Γ ⊢ absurd e ⇐ C
voidElim :: Synth -> Check
voidElim (Synth synth) = Check $ \ty -> do
  (scrutTy, scrut) <- synth
  case scrutTy of
    VVoidTy -> do
      ty <- quoteValue (VUniv (VLNat 0)) ty
      pure $ SAbsurd ty scrut
    _ -> throwError $ TypeError $ "Expected a Void but got: " <> show scrutTy

-- | Sum Formation Synth
--
-- Sum type. Synthesizes both components, extracts their universe levels, and
-- returns the maximum. Elaborates to @SSumTy sa sb@.
--
--  Γ ⊢ A ⇒ Type n    Γ ⊢ B ⇒ Type m
--  ─────────────────────────────────── Sum⇒
--       Γ ⊢ A + B ⇒ Type (max n m)
sumFormationSynth :: Synth -> Synth -> Synth
sumFormationSynth (Synth lTac) (Synth rTac) = Synth $ do
  (lTy, sa) <- lTac
  n <- expectUniv lTy

  (rTy, sb) <- rTac
  m <- expectUniv rTy

  pure (VUniv (vlmax n m), SSumTy sa sb)

-- | Sum Formation Check
--
-- Sum type. Both components are checked against the goal universe level.
-- Cumulativity ensures this accepts components at any lower level. Elaborates
-- to @SSumTy sa sb@.
--
--  Γ ⊢ A ⇐ Type k    Γ ⊢ B ⇐ Type k
--  ─────────────────────────────────── Sum⇐
--       Γ ⊢ A + B ⇐ Type k
sumFormationCheck :: Check -> Check -> Check
sumFormationCheck (Check lTac) (Check rTac) = Check $ \case
  VUniv k -> do
    sa <- lTac (VUniv k)
    sb <- rTac (VUniv k)

    pure (SSumTy sa sb)
  ty ->
    throwError $
      TypeError $
        "Expected a Type, but got: " <> show ty

-- | Sum Left Introduction
--
-- Checked against a sum type. The payload is checked against the left
-- component.
--
--      Γ ⊢ e ⇐ A
--  ───────────────── InL⇐
--  Γ ⊢ InL e ⇐ A + B
sumIntroL :: Check -> Check
sumIntroL (Check check) = Check $ \case
  VSumTy a _b -> SInL <$> check a
  ty -> throwError $ TypeError $ "Expected a Sum type but got: " <> show ty

-- | Sum Right Introduction
--
-- Checked against a sum type. The payload is checked against the right
-- component.
--
--  Γ ⊢ e ⇐ B
--  ──────────────── InR⇐
--  Γ ⊢ InR e ⇐ A + B
sumIntroR :: Check -> Check
sumIntroR (Check check) = Check $ \case
  VSumTy _a b -> SInR <$> check b
  ty -> throwError $ TypeError $ "Expected a Sum type but got: " <> show ty

-- | Sum Elimination
--
-- Synthesize the scrutinee's sum type, then check each branch as a function
-- from the injection's payload type to the motive. The branches are elaborated
-- as lambdas that bind the payload.
--
--  Γ ⊢ e ⇒ A + B    Γ ⊢ f ⇐ A → C    Γ ⊢ g ⇐ B → C
--  ─────────────────────────────────────────────── SumCase⇐
--                Γ ⊢ SumCase e f g ⇐ C
sumElim :: Synth -> Check -> Check -> Check
sumElim (Synth synth) (Check checkT1) (Check checkT2) = Check $ \motiv -> do
  (scrutTy, scrut) <- synth
  case scrutTy of
    VSumTy a b -> do
      f <- checkT1 (VFuncTy a motiv)
      g <- checkT2 (VFuncTy b motiv)
      motiv <- quoteValue (VUniv (VLNat 0)) motiv
      pure $ SSumCase scrut motiv f g
    _ -> throwError $ TypeError $ "Expected a Sum type but got: " <> show scrutTy

-- | Natural Type Formation
--
-- ─────────────────── Nat⇒
-- Γ ⊢ Nat ⇒ Type 0
natFormation :: Synth
natFormation = Synth $ pure (VUniv (VLNat 0), SNaturalTy)

-- | Integer Type Formation
--
-- ─────────────────── Int⇒
-- Γ ⊢ Int ⇒ Type 0
intFormation :: Synth
intFormation = Synth $ pure (VUniv (VLNat 0), SIntegerTy)

-- | Real Type Formation
--
-- ────────────────── Real⇒
-- Γ ⊢ Real ⇒ Type 0
realFormation :: Synth
realFormation = Synth $ pure (VUniv (VLNat 0), SRealTy)

-- | Natural Introduction
--
-- Checked against 'NaturalTy' (or a supertype via subtyping, e.g. 'IntegerTy'
-- or 'RealTy'). Validates that the literal is non-negative.
--
-- ───────── ℕ⇐
-- Γ ⊢ n ⇐ ℕ
natIntro :: Integer -> Check
natIntro n = Check $ \case
  VNaturalTy ->
    if n >= 0
      then pure (SNatural n)
      else throwError $ TypeError "Naturals must be greater then or equal to zero."
  ty -> do
    ok <- checkSubtype VNaturalTy ty
    if ok
      then pure (SNatural n)
      else throwError $ TypeError $ "'Natural' cannot be a subtype of '" <> show ty <> "'"

-- | Integer Introduction
--
-- Checked against 'IntegerTy' (or a supertype via subtyping, e.g. 'RealTy').
--
-- ──────── ℤ⇐
-- Γ ⊢ z ⇐  ℤ
intIntro :: Integer -> Check
intIntro z = Check $ \case
  VIntegerTy -> pure (SInteger z)
  ty -> do
    ok <- checkSubtype VIntegerTy ty
    if ok
      then pure (SInteger z)
      else throwError $ TypeError $ "'Integer' cannot be a subtype of '" <> show ty <> "'"

-- | Real Introduction
--
-- Checked against 'RealTy' (or a supertype via subtyping).
--
-- ───────── ℝ⇐
-- Γ ⊢ r ⇐ ℝ
realIntro :: Scientific -> Check
realIntro r = Check $ \case
  VRealTy -> pure (SReal r)
  ty -> do
    ok <- checkSubtype VRealTy ty
    if ok
      then pure (SReal r)
      else throwError $ TypeError $ "'Real' cannot be a subtype of '" <> show ty <> "'"

-- | Record Type Formation Synth
--
-- Record type. Synthesizes each field type, extracts their universe levels, and
-- returns the maximum. An empty record lives at @Type 0@. Elaborates to
-- @SRecordTy fields'@.
--
--  Γ ⊢ A₁ ⇒ Type n₁    ...    Γ ⊢ Aₖ ⇒ Type nₖ
--  ──────────────────────────────────────────────── Record⇒
--     Γ ⊢ { l₁ : A₁, ..., lₖ : Aₖ } ⇒ Type (max n₁ ... nₖ)
recordFormationSynth :: [(Name, Synth)] -> Synth
recordFormationSynth fields = Synth $ do
  res <- forM fields $ \(nm, Synth tac) -> do
    (sty, sa) <- tac
    n <- expectUniv sty
    pure (n, (nm, sa))
  let (lvls, fields') = unzip res
  pure (VUniv (foldLevels lvls), SRecordTy fields')

-- | Record Type Formation Check
--
-- Record type. All field types are checked against the goal universe level.
-- Cumulativity ensures this accepts fields at any lower level. Elaborates to
-- @SRecordTy fields'@.
--
--  Γ ⊢ A₁ ⇐ Type k    ...    Γ ⊢ Aₖ ⇐ Type k
--  ──────────────────────────────────────────────── Record⇐
--     Γ ⊢ { l₁ : A₁, ..., lₖ : Aₖ } ⇐ Type k
recordFormationCheck :: [(Name, Check)] -> Check
recordFormationCheck fields = Check $ \case
  VUniv k -> do
    fields' <- forM fields $ \(nm, Check tac) -> do
      sa <- tac (VUniv k)

      pure (nm, sa)

    pure (SRecordTy fields')
  ty ->
    throwError $
      TypeError $
        "Expected a Type, but got: " <> show ty

-- | Record Introduction
--
-- Checked against a record type. Uses 'alignWithM' to match the term's fields
-- against the type's fields via a 'Map'. 'These' means both present (check the
-- field), 'This' means a field in the type but not the term (missing field
-- error), 'That' means a field in the term but not the type (extra field
-- error). Field order is irrelevant because both sides are converted to maps
-- before alignment.
--
--         for each i  Γ ⊢ tᵢ ⇐ Tᵢ
-- ─────────────────────────────────────── Record⇐
-- Γ ⊢ { lᵢ = tᵢ} ⇐ { lᵢ : Tᵢ (i ∈ I..n) }
recordIntro :: [(Name, (Term, Check))] -> Check
recordIntro fields = Check $ \case
  VRecordTy ty -> do
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

-- | Record Elimination
--
-- Synthesize the record's type, then look up the projected field by name. A
-- synth rule because the record's type tells us the field's type.
--
-- Γ ⊢ t₁ ⇒ { lᵢ : Tᵢ (i ∈ I..n) }
-- ─────────────────────────────── Get⇒
--       Γ ⊢ Get lⱼ t₁ ⇒ Tⱼ
recordElim :: Name -> Synth -> Synth
recordElim name (Synth fieldTac) =
  Synth $
    fieldTac >>= \case
      (VRecordTy fields, tm) ->
        case lookup name fields of
          Just ty -> pure (ty, SGet name tm)
          Nothing -> throwError $ TypeError $ "Record does not contain a field called " <> show name
      (ty, _) -> throwError $ TypeError $ "Expected a record type but got " <> show ty

-- | ADT Type Formation Synth
--
-- ADT type applied to type arguments. Synthesizes each type argument, extracts
-- their universe levels, and returns the maximum. Constructor fields are not
-- inspected at formation time. Elaborates to @SAdtTy nm tys'@.
--
--  Γ ⊢ T₁ ⇒ Type n₁    ...    Γ ⊢ Tₖ ⇒ Type nₖ
--  ──────────────────────────────────────────────── ADT⇒
--       Γ ⊢ T T₁...Tₖ ⇒ Type (max n₁ ... nₖ)
adtFormationSynth :: Name -> [Synth] -> Synth
adtFormationSynth nm tys = Synth $ do
  res <- forM tys $ \(Synth tac) -> do
    (ty, s) <- tac
    n <- expectUniv ty
    pure (n, s)
  let (lvls, tys') = unzip res
  pure (VUniv (foldLevels lvls), SAdtTy nm tys')

-- | ADT Type Formation Check
--
-- ADT type applied to type arguments. All type arguments are checked against
-- the goal universe level. Cumulativity ensures this accepts arguments at any
-- lower level. Elaborates to @SAdtTy nm tys'@.
--
--  Γ ⊢ T₁ ⇐ Type k    ...    Γ ⊢ Tₖ ⇐ Type k
--  ──────────────────────────────────────────────── ADT⇐
--       Γ ⊢ T T₁...Tₖ ⇐ Type k
adtFormationCheck :: Name -> [Check] -> Check
adtFormationCheck nm tys = Check $ \case
  VUniv k -> do
    tys' <- forM tys $ \(Check tac) -> tac (VUniv k)

    pure (SAdtTy nm tys')
  ty ->
    throwError $
      TypeError $
        "Expected a Type, but got: " <> show ty

-- | ADT Introduction
--
-- Checked against a type whose return position is an ADT type. The expected
-- type is decomposed by peeling off function arrows until the return type @T ā@
-- is found. The type arguments @ā@ are extracted and substituted into the
-- constructor's field types.
--
-- Supports partial application via eta expansion. When fewer than @n@ term
-- arguments are provided, the constructor is wrapped in lambdas for all @n@
-- fields and the provided arguments are applied, leaving a function that
-- accepts the remaining fields.
--
-- For example, given @data Maybe a = Nothing | Just a@:
--
-- @(Just True : Maybe Bool)@: the expected type is @Maybe Bool@, so @TyParam 0@
-- is instantiated to @Bool@, and @True@ is checked against @Bool@.
--
-- @(Just : Bool -> Maybe Bool)@: the expected type is @Bool -> Maybe Bool@. The
-- return position is @Maybe Bool@, giving @ā = [Bool]@. No term arguments are
-- provided, so @Just@ is eta-expanded to @λx. Just x@.
--
-- Implementation:
-- 1. Decompose the expected type to find @SAdtTy tyName tys@ at the return
--    position.
-- 2. Check that @length tys@ matches the ADT's arity.
-- 3. Look up the constructor spec for @C@.
-- 4. Build the constructor's function type using 'buildConstrType', which
--    substitutes @tys@ for 'TyParam' references and the full ADT type for
--    'Rec'.
-- 5. Eta-expand the constructor for all @n@ fields.
-- 6. Check each provided argument against its field type.
-- 7. Apply the checked arguments to the eta-expanded constructor.
--
-- C has fields T₁...Tₙ in spec for T
-- Γ ⊢ tᵢ ⇐ Tᵢ[ā] (i ∈ 1..m, m ≤ n)
-- ──────────────────────────────────────────────── Cnstr⇐
-- Γ ⊢ (λ[x₁...xₙ]. C x₁...xₙ) t₁...tₘ
--   ⇐ Tₘ₊₁[ā] → ... → Tₙ[ā] → T ā
adtIntro :: Name -> [Check] -> Check
adtIntro nm chks = Check $ \expectedTy -> do
  let (returnTy, _) = decomposeFunction expectedTy
  case returnTy of
    VAdtTy tyName tys ->
      lookupDataTypeSpec nm $ \(DataTypeSpec _ arity _) -> do
        when (length tys /= arity) $
          throwError $
            TypeError $
              "Type '"
                <> show tyName
                <> "' expects "
                <> show arity
                <> " type arguments but got "
                <> show (length tys)
        lookupDataCnstrSpec nm $ \dataConstrSpec -> do
          ctx <- ask
          let constrTy = buildConstrType (toEvalEnv ctx) tyName tys dataConstrSpec
              (_returnTy, paramTys) = decomposeFunction constrTy
          when (length chks > length paramTys) $
            throwError $
              TypeError $
                "Data Constructor '"
                  <> show nm
                  <> "' expects "
                  <> show (length paramTys)
                  <> " arguments but got "
                  <> show (length chks)
          let scnstr = etaExpandCnstr (length paramTys) (SCnstr nm [])
          params <- zipWithM runCheck chks paramTys
          pure $ foldl' SAp scnstr params
    ty -> throwError $ TypeError $ "Expected an ADT type but got: " <> show ty

-- | ADT Elimination
--
-- The core idea is that given an ADT:
--
-- data ListBool = Nil | Cons Bool ListBool
--
-- We want to build an eliminator function:
--
-- list-bool-elim : A -> (Bool -> A -> A) -> ListBool -> A
--
-- NOTE: The 'Nil' eliminator ought to be '() -> A' but that is isomorphic to
-- 'A' so we can simplify it.
--
-- The 'DataTypeSpec' for ListBool is:
--
-- Data "ListBool" [Constr "Nil" [], Constr "Just" [Term BoolTy, Rec []]]
--
-- From this we derive the recursion principle for our eliminator. The elminator
-- receives one function per Data Constructor which returns our goal type 'A'.
-- The parameters on the constructor become parameters on the function where
-- recursive references are replaced by the goal type:
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
adtElim :: Synth -> [(Name, Check)] -> Check
adtElim scrut cases = Check $ \motive -> do
  (scrutTy, scrut') <- runSynth scrut
  case scrutTy of
    VAdtTy tyName tys ->
      lookupDataTypeSpecByType tyName $ \dataSpec -> do
        ctx <- ask
        let eliminators = Map.fromList $ mkEliminator (toEvalEnv ctx) motive dataSpec tys
            checks = Map.fromList cases
            alignCases = \case
              These ty chk -> runCheck chk ty
              This _ty -> throwError $ TypeError $ "Missing case for constructor of type '" <> show tyName <> "'"
              That _chk -> throwError $ TypeError $ "Extra case branch not in type '" <> show tyName <> "'"
        cases' <- Map.toList <$> alignWithM alignCases eliminators checks
        pure $ SCase scrut' cases'
    ty -> throwError $ TypeError $ "Expected an ADT type but got: " <> show ty

-- | Build a function type from a 'DataConstructorSpec'
buildConstrType :: EvalEnv -> Name -> [Value] -> DataConstructorSpec -> Value
buildConstrType _ tyName tys (Constr _nm []) = VAdtTy tyName tys
buildConstrType ctx tyName tys (Constr nm (Term x : xs)) =
  let vx = runEvalM (eval x) ctx
   in VFuncTy vx $ buildConstrType ctx tyName tys (Constr nm xs)
buildConstrType ctx tyName tys (Constr nm (Rec : xs)) = VFuncTy (VAdtTy tyName tys) $ buildConstrType ctx tyName tys (Constr nm xs)
buildConstrType ctx tyName tys (Constr nm (TyParam n : xs)) = VFuncTy (tys !! n) $ buildConstrType ctx tyName tys (Constr nm xs)

-- | Decompose a function into its return type and a list of its args.
decomposeFunction :: Value -> (Value, [Value])
decomposeFunction (VFuncTy a b) = (a :) <$> decomposeFunction b
decomposeFunction ty = (ty, [])

-- | Eta Expand around a data constructor.
etaExpandCnstr :: Int -> Syntax -> Syntax
etaExpandCnstr n t = uncurry ($) $ go n (id, t)
  where
    go 0 (f, t) = (f, t)
    go n (f, SCnstr nm xs) = go (n - 1) (SLam (Name "_") . f, SCnstr nm (xs <> [SVar (Ix $ n - 1)]))
    go _ _ = error "impossible case"

mkEliminator :: EvalEnv -> Value -> DataTypeSpec -> [Value] -> [(Name, Value)]
mkEliminator ctx motiveTy (DataTypeSpec tyName _airity specs) tys =
  fmap (mkConstrEliminator ctx tyName tys motiveTy) specs

mkConstrEliminator :: EvalEnv -> Name -> [Value] -> Value -> DataConstructorSpec -> (Name, Value)
mkConstrEliminator ctx tyName tys motiveTy (Constr nm args) =
  ( nm,
    foldr
      ( flip $ \acc -> \case
          Term ty -> VFuncTy (runEvalM (eval ty) ctx) acc
          Rec -> VAdtTy tyName tys `VFuncTy` acc
          TyParam ix -> (tys !! ix) `VFuncTy` acc
      )
      motiveTy
      args
  )

--------------------------------------------------------------------------------
-- Subsumption
--
-- Subsumption is the mechanism that connects subtyping to typechecking. The sub
-- tactic (used in 'check') synthesizes a type for a term and then verifies
-- that the synthesized type is a subtype of the expected type. If it is, the
-- term passes through unchanged.
--
-- This is subsumptive (not coercive) subtyping: no conversion term is inserted
-- during elaboration. It works because all our subtypes share the same runtime
-- representation (e.g., a natural literal is already a valid integer literal).
-- A coercive system would need to wrap the term in a conversion function when
-- the representations differ (e.g., Peano nats to machine integers).
--
-- The subtyping judgment itself is defined by 'isSubtypeOf' below, with
-- dedicated tactics for records (width and depth) and functions
-- (contravariant in the domain, covariant in the codomain).

-- | The subtyping relationship T₁ <: T₂ can be read as "T₁ is a subtype of T₂".
-- It can be understood as stating that anywhere a T₂ can be used, we can use a
-- T₁.
isSubtypeOf :: Lvl Value -> Value -> Value -> EvalM Bool
isSubtypeOf _ (VUniv n) (VUniv m) = pure (n <= m)
isSubtypeOf l (VPi _ a1 clo1) (VPi _ a2 clo2) = do
  domOk <- isSubtypeOf l a2 a1
  let x = VNeutral a2 $ Neutral (VVar l) Nil
  cod1 <- appClosure clo1 x
  cod2 <- appClosure clo2 x
  codOk <- isSubtypeOf (incLevel l) cod1 cod2
  pure (domOk && codOk)
isSubtypeOf l s@VFuncTy {} t@VFuncTy {} = functionSubtype l s t
isSubtypeOf l (VSigma _ a1 clo1) (VSigma _ a2 clo2) = do
  fstOk <- isSubtypeOf l a1 a2
  let x = VNeutral a1 $ Neutral (VVar l) Nil
  b1 <- appClosure clo1 x
  b2 <- appClosure clo2 x
  sndOk <- isSubtypeOf (incLevel l) b1 b2
  pure (fstOk && sndOk)
isSubtypeOf _ VNaturalTy VIntegerTy = pure True
isSubtypeOf _ VNaturalTy VRealTy = pure True
isSubtypeOf _ VIntegerTy VRealTy = pure True
isSubtypeOf l s@VRecordTy {} t@VRecordTy {} = recordSubtype l s t
isSubtypeOf l (VNeutral _ n1) (VNeutral _ n2) = equateNeutral l n1 n2
isSubtypeOf l s t = equateValue l s t

-- | Check two neutrals for definitional equality. Compares heads
-- by structural equality and walks the spines pairwise.
equateNeutral :: Lvl Value -> Neutral -> Neutral -> EvalM Bool
equateNeutral l (Neutral h1 s1) (Neutral h2 s2) =
  if h1 == h2
    then equateSpine l s1 s2
    else pure False

-- | Walk two spines pairwise, checking each frame for equality.
-- Mismatched lengths return 'False'.
equateSpine :: Lvl Value -> SnocList Frame -> SnocList Frame -> EvalM Bool
equateSpine _ Nil Nil = pure True
equateSpine l (Snoc s1 f1) (Snoc s2 f2) = do
  restOk <- equateSpine l s1 s2
  frameOk <- equateFrame l f1 f2
  pure (restOk && frameOk)
equateSpine _ _ _ = pure False

-- | Check two eliminator frames for definitional equality.
-- Uses 'equateValue' (not subtyping) for values in the spine,
-- since we can't determine the variance of a stuck head.
equateFrame :: Lvl Value -> Frame -> Frame -> EvalM Bool
equateFrame l (VApp _ v1) (VApp _ v2) = equateValue l v1 v2
equateFrame _ VFst VFst = pure True
equateFrame _ VSnd VSnd = pure True
equateFrame l (VIf _ t1a t1b) (VIf _ t2a t2b) = do
  a <- equateValue l t1a t2a
  b <- equateValue l t1b t2b
  pure (a && b)
equateFrame l (VAbsurd v1) (VAbsurd v2) =
  equateValue l v1 v2
equateFrame l (VSumCase _ _ _ f1 g1) (VSumCase _ _ _ f2 g2) = do
  a <- equateValue l f1 f2
  b <- equateValue l g1 g2
  pure (a && b)
equateFrame _ (VGet n1) (VGet n2) = pure (n1 == n2)
equateFrame l (VCase _ cs1) (VCase _ cs2) =
  allM
    ( \((n1, v1), (n2, v2)) ->
        if n1 == n2
          then equateValue l v1 v2
          else pure False
    )
    (zip cs1 cs2)
equateFrame _ _ _ = pure False

-- | Definitional equality on values. Symmetric, unlike
-- 'isSubtypeOf'. Goes under binders by creating fresh
-- variables and instantiating closures. Used by
-- 'equateFrame' for comparing values in neutral spines.
equateValue :: Lvl Value -> Value -> Value -> EvalM Bool
equateValue l (VNeutral _ n1) (VNeutral _ n2) =
  equateNeutral l n1 n2
equateValue l (VLam _ clo1) (VLam _ clo2) = do
  let x = VNeutral VUnit $ Neutral (VVar l) Nil
  b1 <- appClosure clo1 x
  b2 <- appClosure clo2 x
  equateValue (incLevel l) b1 b2
equateValue _ (VUniv n) (VUniv m) = pure (n == m)
equateValue l (VPi _ a1 clo1) (VPi _ a2 clo2) = do
  aOk <- equateValue l a1 a2
  let x = VNeutral a1 $ Neutral (VVar l) Nil
  b1 <- appClosure clo1 x
  b2 <- appClosure clo2 x
  bOk <- equateValue (incLevel l) b1 b2
  pure (aOk && bOk)
equateValue l (VFuncTy a1 b1) (VFuncTy a2 b2) = do
  aOk <- equateValue l a1 a2
  bOk <- equateValue l b1 b2
  pure (aOk && bOk)
equateValue l (VSigma _ a1 clo1) (VSigma _ a2 clo2) = do
  aOk <- equateValue l a1 a2
  let x = VNeutral a1 $ Neutral (VVar l) Nil
  b1 <- appClosure clo1 x
  b2 <- appClosure clo2 x
  bOk <- equateValue (incLevel l) b1 b2
  pure (aOk && bOk)
equateValue l (VPairTy a1 b1) (VPairTy a2 b2) = do
  aOk <- equateValue l a1 a2
  bOk <- equateValue l b1 b2
  pure (aOk && bOk)
equateValue l (VPair a1 b1) (VPair a2 b2) = do
  p <- equateValue l a1 a2
  q <- equateValue l b1 b2
  pure (p && q)
equateValue _ VBoolTy VBoolTy = pure True
equateValue _ VTru VTru = pure True
equateValue _ VFls VFls = pure True
equateValue _ VUnitTy VUnitTy = pure True
equateValue _ VUnit VUnit = pure True
equateValue _ VVoidTy VVoidTy = pure True
equateValue l (VSumTy a1 b1) (VSumTy a2 b2) = do
  aOk <- equateValue l a1 a2
  bOk <- equateValue l b1 b2
  pure (aOk && bOk)
equateValue l (VInL a1) (VInL a2) = equateValue l a1 a2
equateValue l (VInR b1) (VInR b2) = equateValue l b1 b2
equateValue _ VNaturalTy VNaturalTy = pure True
equateValue _ VIntegerTy VIntegerTy = pure True
equateValue _ VRealTy VRealTy = pure True
equateValue _ (VNatural a) (VNatural b) = pure (a == b)
equateValue _ (VInteger a) (VInteger b) = pure (a == b)
equateValue _ (VReal a) (VReal b) = pure (a == b)
equateValue l (VRecordTy fs1) (VRecordTy fs2) =
  allM
    ( \((n1, t1), (n2, t2)) ->
        if n1 == n2
          then equateValue l t1 t2
          else pure False
    )
    (zip fs1 fs2)
equateValue l (VRecord fs1) (VRecord fs2) = do
  allM
    ( \((n1, v1), (n2, v2)) ->
        if n1 == n2
          then equateValue l v1 v2
          else pure False
    )
    (zip fs1 fs2)
equateValue l (VAdtTy n1 ts1) (VAdtTy n2 ts2) =
  if n1 == n2
    then allM (uncurry (equateValue l)) (zip ts1 ts2)
    else pure False
equateValue l (VCnstr n1 as1) (VCnstr n2 as2) =
  if n1 == n2
    then allM (uncurry (equateValue l)) (zip as1 as2)
    else pure False
equateValue _ _ _ = pure False

-- | Function Subtyping
--
-- A subtype of T₁ → T₂ is any type S₁ → S₂ such that T₁ <: S₁ and S₂ <: T₂.
--
-- For example:
--
-- (ℤ → ℕ) <: (ℕ → ℤ)
--
-- These feels backwards at first glance, but the received parameter T₁/S₁ is
-- contravariant. This reverses the subtyping relationship.
--
-- Another way of stating the example above is that you can replace a function ℕ
-- → ℤ with a function ℤ → ℕ.
--
-- This works because any ℕ you would have applied to the supertype function is
-- also an ℤ which can also be applied to the subtype function.
--
-- Likewise the ℕ produced by the subtype function is also a ℤ and thus
-- satisfies the super type's return param.
--
-- Thus our typing rule for function subtyping is:
--
-- T₁ <: S₁  S₂ <: T₂
-- ────────────────── Func-Sub
-- S₁ → S₂ <: T₁ → T₂
functionSubtype :: Lvl Value -> Value -> Value -> EvalM Bool
functionSubtype l (s1 `VFuncTy` s2) (t1 `VFuncTy` t2) = do
  domOk <- isSubtypeOf l t1 s1
  codOk <- isSubtypeOf l s2 t2
  pure (domOk && codOk)
functionSubtype _ _ _ = error "impossible case in functionSubtype"

-- | Record Depth Subtyping
--
-- Any field of a record can be replaced by its subtype. Since any operation
-- supported for a field in the supertype is supported for its subtype, any
-- operation feasible on the record supertype is supported by the record
-- subtype.
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
-- Record width subtyping falls out of 'Map.isSubmapOfBy': the expected record's
-- keys must be a subset of the actual record's keys, so extra fields in the
-- actual record are ignored.
--
-- { foo :: Nat, bar :: Bool } <: { foo :: Nat }
recordSubtype :: Lvl Value -> Value -> Value -> EvalM Bool
recordSubtype l (VRecordTy s) (VRecordTy t) = do
  let s' = Map.fromList s
      t' = Map.fromList t
  allM
    ( \(k, tv) ->
        case Map.lookup k s' of
          Nothing -> pure False
          Just sv -> isSubtypeOf l sv tv
    )
    (Map.toList t')
recordSubtype _ _ _ = error "impossible case in recordSubtype"

--------------------------------------------------------------------------------
-- Evaluator
--
-- The evaluator operates on 'Syntax' (the elaborated core IR) rather than
-- 'Term'. This is why elaboration matters, the evaluator doesn't need to deal
-- with named variables, annotations, or let bindings. It just sees de Bruijn
-- indices, lambdas, and applications.
--
-- Evaluation maps 'Syntax' to 'Value' under an environment. The interesting
-- cases are:
--
-- - 'SVar': look up the value in the environment by de Bruijn index.
-- - 'SLam': capture the current environment in a closure (don't evaluate the
--           body yet, since we don't know the argument).
-- - 'SAp': evaluate both sides, then apply. This is where beta reduction
--          happens, by instantiating the closure with the argument.
--
-- Subtyping is a typechecking concern and does not affect evaluation.
--
-- Constructors evaluate to 'VCnstr' by evaluating each argument. Case
-- expressions evaluate the scrutinee, match on the 'VCnstr' name, and apply the
-- branch body to the constructor's arguments. A case on a neutral produces a
-- stuck 'VCase' frame.

newtype EvalM a = EvalM {runEvalM :: EvalEnv -> a}
  deriving
    (Functor, Applicative, Monad, MonadReader EvalEnv)
    via Reader EvalEnv

eval :: Syntax -> EvalM Value
eval = \case
  -- Core
  SVar (Ix ix) -> do
    env <- asks envValues
    pure $ fromMaybe (error "internal error") $ nth env ix
  SLam bndr body -> do
    env <- ask
    pure $ VLam bndr (Closure env body)
  SAp tm1 tm2 -> do
    fun <- eval tm1
    arg <- eval tm2
    doApply fun arg
  SHole sty -> do
    vty <- eval sty
    pure $ VNeutral vty (Neutral (VHole sty) Nil)
  -- Universe
  SUniv l -> VUniv <$> evalLevel l
  -- Pi / Function
  SPi nm a b -> do
    env <- ask
    a <- eval a
    pure $ VPi nm a $ Closure env b
  SFuncTy t1 t2 -> do
    t1 <- eval t1
    t2 <- eval t2
    pure $ VFuncTy t1 t2
  SLevelPi nm sa -> do
    env <- ask
    pure $ VLevelPi nm $ LevelClosure env sa
  SLevelLam nm sa -> do
    env <- ask
    pure $ VLevelLam nm $ LevelClosure env sa
  SLevelAp sa sl -> do
    va <- eval sa
    vl <- evalLevel sl
    doLevelApply va vl
  -- Sigma / Pair
  SSigma nm a b -> do
    env <- ask
    a <- eval a
    pure $ VSigma nm a $ Closure env b
  SPairTy t1 t2 -> do
    t1 <- eval t1
    t2 <- eval t2
    pure $ VPairTy t1 t2
  SPair tm1 tm2 -> do
    tm1' <- eval tm1
    tm2' <- eval tm2
    pure $ VPair tm1' tm2'
  SFst tm -> eval tm >>= doFst
  SSnd tm -> eval tm >>= doSnd
  -- Bool
  SBoolTy -> pure VBoolTy
  STru -> pure VTru
  SFls -> pure VFls
  SIf p motiv t1 t2 -> do
    p' <- eval p
    t1' <- eval t1
    t2' <- eval t2
    motiv <- eval motiv
    doIf p' motiv t1' t2'
  -- Unit
  SUnitTy -> pure VUnitTy
  SUnit -> pure VUnit
  -- Void
  SVoidTy -> pure VVoidTy
  SAbsurd ty tm -> do
    tm' <- eval tm
    doSumAbsurd tm' ty
  -- Sum
  SSumTy t1 t2 -> do
    t1 <- eval t1
    t2 <- eval t2
    pure $ VSumTy t1 t2
  SInL tm -> VInL <$> eval tm
  SInR tm -> VInR <$> eval tm
  SSumCase t1 motive t2 t3 -> do
    t1' <- eval t1
    t2' <- eval t2
    t3' <- eval t3
    doSumCase t1' motive t2' t3'
  -- Numerics
  SNaturalTy -> pure VNaturalTy
  SIntegerTy -> pure VIntegerTy
  SRealTy -> pure VRealTy
  SNatural n -> pure $ VNatural n
  SInteger z -> pure $ VInteger z
  SReal r -> pure $ VReal r
  -- Records
  SRecordTy fields -> do
    fields <- forM fields $ \(nm, ty) -> (nm,) <$> eval ty
    pure $ VRecordTy fields
  SRecord fields -> doRecord fields
  SGet name tm -> eval tm >>= doGet name
  -- ADTs
  SAdtTy nm tys -> do
    tys <- traverse eval tys
    pure $ VAdtTy nm tys
  SCnstr nm bndrs -> doConstructor nm bndrs
  SCase scrut patterns -> doCase scrut patterns

doApply :: Value -> Value -> EvalM Value
doApply (VLam _ clo) arg = appClosure clo arg
doApply (VNeutral (VFuncTy ty1 ty2) neu) arg = pure $ VNeutral ty2 (pushFrame neu (VApp ty1 arg))
doApply (VNeutral (VPi _ a clo) neu) arg = do
  fiber <- appClosure clo arg
  pure $ VNeutral fiber (pushFrame neu (VApp a arg))
doApply _ _ = error "impossible case in doApply"

doLevelApply :: Value -> VLevel -> EvalM Value
doLevelApply (VLevelLam _ clo) vl = appLevelClosure clo vl
doLevelApply (VNeutral (VLevelPi _ clo) neu) vl = do
  fiber <- appLevelClosure clo vl
  pure $ VNeutral fiber (pushFrame neu (VLevelApp vl))
doLevelApply _ _ = error "impossible case in doLevelApply"

doFst :: Value -> EvalM Value
doFst (VPair a _b) = pure a
doFst _ = error "impossible case in doFst"

doSnd :: Value -> EvalM Value
doSnd (VPair _a b) = pure b
doSnd _ = error "impossible case in doSnd"

doSumCase :: Value -> Syntax -> Value -> Value -> EvalM Value
doSumCase (VInL v) _motive f _ = doApply f v
doSumCase (VInR v) _motive _ g = doApply g v
doSumCase (VNeutral (VSumTy a b) neu) motive f g = do
  motive <- eval motive
  pure $ VNeutral motive (pushFrame neu (VSumCase (VFuncTy a motive) (VFuncTy b motive) motive f g))
doSumCase _ _ _ _ = error "impossible case in doSumCase"

doSumAbsurd :: Value -> Syntax -> EvalM Value
doSumAbsurd (VNeutral _ neu) sty = do
  vty <- eval sty
  pure $ VNeutral vty (pushFrame neu (VAbsurd vty))
doSumAbsurd _ _ = error "impossible case in doSumAbsurd"

doIf :: Value -> Value -> Value -> Value -> EvalM Value
doIf VTru _motive t1 _ = pure t1
doIf VFls _motive _ t2 = pure t2
doIf (VNeutral ty neu) motive t1 t2 = pure $ VNeutral motive (pushFrame neu (VIf ty t1 t2))
doIf _ _ _ _ = error "impossible case in doIf"

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
doCase scrut patterns = do
  scrut' <- eval scrut
  case scrut' of
    VCnstr nm args -> do
      case find ((== nm) . fst) patterns of
        Just (_, body) -> do
          body' <- eval body
          foldM doApply body' args
        Nothing -> error "impossible case in doCase: missing branch"
    VNeutral ty neu -> do
      branches <- traverse (traverse eval) patterns
      pure $ VNeutral ty (pushFrame neu (VCase ty branches))
    _ -> error "impossible case in doCase: non-constructor scrutinee"

-- | Instantiate a closure by extending the env with a value and
-- evaluating the body.
appClosure :: Closure -> Value -> EvalM Value
appClosure (Closure env body) v =
  local (const $ env {envValues = Snoc env.envValues v, envValuesLen = env.envValuesLen + 1}) $ eval body

appLevelClosure :: LevelClosure -> VLevel -> EvalM Value
appLevelClosure (LevelClosure env body) l =
  local (const $ env {envLevels = Snoc env.envLevels l, envLevelsLen = env.envLevelsLen + 1}) $ eval body

evalLevel :: SLevel -> EvalM VLevel
evalLevel (SLNat n) = pure $ VLNat n
evalLevel (SLVar (Ix ix)) = do
  env <- asks envLevels
  pure $ fromMaybe (error "internal error") $ nth env ix
evalLevel (SLMax a b) = vlmax <$> evalLevel a <*> evalLevel b
evalLevel (SLSucc a) = vlsucc <$> evalLevel a
evalLevel (SLOmega n) = pure (VLOmega n)

--------------------------------------------------------------------------------
-- Quoting
--
-- Quoting reads back a 'Value' into 'Syntax' (normal form). It
-- is type-directed: the 'Value' type argument tells us how to
-- handle each value.
--
-- Key cases dispatch on the type:
--
-- 1. At 'VFuncTy' or 'VPi': eta-expand. Generate a fresh
--    variable at the domain type, apply the value to it, quote
--    the result at the codomain. For 'VPi' the codomain comes
--    from instantiating the closure. Produces 'SLam'.
-- 2. At 'VPairTy' or 'VSigma': quote each component at its
--    type. For 'VSigma' the second component's type comes from
--    instantiating the closure with the first component.
-- 3. At 'VUniv': the value is a type former. Quote its
--    sub-components at 'VUniv'.
-- 4. At any other type: the value should be canonical or
--    neutral. Quote accordingly.
--
-- This ensures normal forms are fully eta-long, so two terms
-- are beta-eta equal iff their normal forms are syntactically
-- identical.
--
-- The 'Lvl' parameter tracks how many binders we've gone under
-- so we can convert de Bruijn levels back to indices.

quote :: Lvl Value -> Lvl VLevel -> Value -> Value -> EvalM Syntax
quote l ll = \cases
  -- Neutral
  _ (VNeutral _ neu) -> quoteNeutral l ll neu
  -- Pi / Function: eta-expand
  (VPi _nm a clo) (VLam bndr body) -> do
    b <- bindVar a l $ \v l' -> do
      fiber <- appClosure clo v
      body' <- appClosure body v
      quote l' ll fiber body'
    pure $ SLam bndr b
  (VPi _nm a clo) f -> do
    b <- bindVar a l $ \v l' -> do
      fiber <- appClosure clo v
      doApply f v >>= quote l' ll fiber
    pure $ SLam "_" b
  (VFuncTy ty1 ty2) (VLam bndr clo@(Closure _env _body)) -> do
    body <- bindVar ty1 l $ \v l' -> do
      clo <- appClosure clo v
      quote l' ll ty2 clo
    pure $ SLam bndr body
  (VFuncTy ty1 ty2) f -> do
    body <- bindVar ty1 l $ \v l' ->
      doApply f v >>= quote l' ll ty2
    pure $ SLam "_" body
  (VLevelPi _nm clo) (VLevelLam bndr body) -> do
    b <- bindLevelVar ll $ \lv ll' -> do
      fiber <- appLevelClosure clo lv
      body' <- appLevelClosure body lv
      quote l ll' fiber body'
    pure $ SLevelLam bndr b
  (VLevelPi _nm clo) f -> do
    b <- bindLevelVar ll $ \lv ll' -> do
      fiber <- appLevelClosure clo lv
      body' <- doLevelApply f lv
      quote l ll' fiber body'
    pure $ SLevelLam "_" b
  _ (VLevelPi nm clo) -> do
    b <- bindLevelVar ll $ \lv ll' -> do
      fiber <- appLevelClosure clo lv
      quote l ll' (VUniv (VLNat 0)) fiber
    pure $ SLevelPi nm b
  -- Sigma / Pair: quote components
  (VSigma _bndr a clo) (VPair tm1 tm2) -> do
    tm1' <- quote l ll a tm1
    fiber <- appClosure clo tm1
    tm2' <- quote l ll fiber tm2
    pure $ SPair tm1' tm2'
  (VPairTy ty1 ty2) (VPair tm1 tm2) -> do
    tm1' <- quote l ll ty1 tm1
    tm2' <- quote l ll ty2 tm2
    pure $ SPair tm1' tm2'
  -- Bool
  _ VTru -> pure STru
  _ VFls -> pure SFls
  -- Unit
  _ VUnit -> pure SUnit
  -- Sum
  (VSumTy a _b) (VInL tm) -> SInL <$> quote l ll a tm
  (VSumTy _a b) (VInR tm) -> SInR <$> quote l ll b tm
  -- Numerics
  _ (VNatural n) -> pure $ SNatural n
  _ (VInteger z) -> pure $ SInteger z
  _ (VReal r) -> pure $ SReal r
  -- Records
  (VRecordTy fieldTys) (VRecord fields) ->
    SRecord
      <$> forM
        fields
        ( \(nm, val) -> do
            case lookup nm fieldTys of
              Just fty -> (nm,) <$> quote l ll fty val
              Nothing -> error "impossible: field not in type."
        )
  -- ADTs
  (VAdtTy tyName tys) (VCnstr nm args) -> do
    ctx <- ask
    case Map.lookup nm ctx.envAdtConstructors of
      Just (DataTypeSpec _ _ specs) ->
        case find (\(Constr cnm _) -> cnm == nm) specs of
          Just spec -> do
            let constrTy = buildConstrType ctx tyName tys spec
                (_, argTys) = decomposeFunction constrTy
            SCnstr nm <$> zipWithM (quote l ll) argTys args
          Nothing -> error "impossible: constructor not in spec"
      Nothing -> error "impossible: constructor not in ADT map"
  -- Quoting types as values (at VUniv)
  _ (VUniv vl) -> pure $ SUniv $ quoteLevel ll vl
  _ (VPi nm a clo) -> do
    a' <- quote l ll (VUniv (VLNat 0)) a
    b' <- bindVar a l $ \v l' -> do
      fiber <- appClosure clo v
      quote l' ll (VUniv (VLNat 0)) fiber
    pure $ SPi nm a' b'
  _ (VFuncTy t1 t2) -> do
    t1 <- quote l ll (VUniv (VLNat 0)) t1
    t2 <- quote l ll (VUniv (VLNat 0)) t2
    pure $ SFuncTy t1 t2
  _ (VSigma bndr a clo) -> do
    a' <- quote l ll (VUniv (VLNat 0)) a
    b <- bindVar a l $ \v l' -> do
      fiber <- appClosure clo v
      quote l' ll (VUniv (VLNat 0)) fiber
    pure $ SSigma bndr a' b
  _ (VPairTy t1 t2) -> do
    t1 <- quote l ll (VUniv (VLNat 0)) t1
    t2 <- quote l ll (VUniv (VLNat 0)) t2
    pure $ SPairTy t1 t2
  _ VBoolTy -> pure SBoolTy
  _ VUnitTy -> pure SUnitTy
  _ VVoidTy -> pure SVoidTy
  _ (VSumTy t1 t2) -> do
    t1 <- quote l ll (VUniv (VLNat 0)) t1
    t2 <- quote l ll (VUniv (VLNat 0)) t2
    pure $ SSumTy t1 t2
  _ VNaturalTy -> pure SNaturalTy
  _ VIntegerTy -> pure SIntegerTy
  _ VRealTy -> pure SRealTy
  _ (VRecordTy fields) -> do
    fields <- forM fields (traverse $ quote l ll (VUniv (VLNat 0)))
    pure $ SRecordTy fields
  _ (VAdtTy nm tys) -> do
    tys <- traverse (quote l ll (VUniv (VLNat 0))) tys
    pure $ SAdtTy nm tys
  -- Catch-all
  ty tm -> error $ "impossible case in quote:\n" <> show ty <> "\n" <> show tm

quoteLvl :: Lvl vsort -> Lvl vsort -> Ix ssort
quoteLvl (Lvl l) (Lvl x) = Ix (l - (x + 1))

quoteNeutral :: Lvl Value -> Lvl VLevel -> Neutral -> EvalM Syntax
quoteNeutral l ll Neutral {..} = foldM (quoteFrame l ll) (quoteHead l head) spine

quoteHead :: Lvl Value -> Head -> Syntax
quoteHead l (VVar lvl) = SVar (quoteLvl l lvl)
quoteHead _ (VHole ty) = SHole ty

quoteFrame :: Lvl Value -> Lvl VLevel -> Syntax -> Frame -> EvalM Syntax
quoteFrame l ll tm = \case
  -- Pi / Function
  VApp ty arg -> SAp tm <$> quote l ll ty arg
  VLevelApp vl ->
    pure $ SLevelAp tm (quoteLevel ll vl)
  -- Sigma / Pair
  VFst -> pure $ SFst tm
  VSnd -> pure $ SSnd tm
  -- Bool
  VIf ty t1 t2 -> do
    sty <- quote l ll (VUniv (VLNat 0)) ty
    liftA2 (SIf tm sty) (quote l ll ty t1) (quote l ll ty t2)
  -- Void
  VAbsurd vty -> do
    sty <- quote l ll (VUniv (VLNat 0)) vty
    pure $ SAbsurd sty tm
  -- Sum
  VSumCase tyF tyG mot f g -> do
    f' <- quote l ll tyF f
    g' <- quote l ll tyG g
    mot <- quote l ll (VUniv (VLNat 0)) mot
    pure $ SSumCase tm mot f' g'
  -- Records
  VGet name -> pure $ SGet name tm
  -- ADTs
  VCase mot cases -> SCase tm <$> traverse (traverse (quote l ll mot)) cases

-- | Introduce a fresh term variable at the given level. Creates a neutral value
-- at the given type and passes it (along with the incremented level) to the
-- continuation. Used by quoting to eta-expand at function types.
bindVar :: Value -> Lvl Value -> (Value -> Lvl Value -> a) -> a
bindVar ty lvl f =
  let v = VNeutral ty $ Neutral (VVar lvl) Nil
   in f v $ incLevel lvl

bindLevelVar :: Lvl VLevel -> (VLevel -> Lvl VLevel -> a) -> a
bindLevelVar l f = do
  f (VLVar l) (incLevel l)

quoteLevel :: Lvl VLevel -> VLevel -> SLevel
quoteLevel _ (VLNat n) = SLNat n
quoteLevel ll (VLVar lvl) = SLVar (quoteLvl ll lvl)
quoteLevel ll (VLMax a b) =
  SLMax (quoteLevel ll a) (quoteLevel ll b)
quoteLevel ll (VLSucc a) = SLSucc (quoteLevel ll a)
quoteLevel _ (VLOmega n) = SLOmega n

--------------------------------------------------------------------------------
-- Main

run :: Term -> Either (Error, Holes) (RunResult Syntax Syntax Syntax, Holes)
run term =
  case runTypecheckM (runSynth $ synth term) initEnv of
    (Left err, holes) -> Left (err, holes)
    (Right (type', syntax), holes) -> do
      let evalEnv = toEvalEnv initEnv
          result = flip runEvalM evalEnv $ do
            value <- eval syntax
            quote initLevel initLevel type' value
          quotedType = runEvalM (quote initLevel initLevel (VUniv (VLNat 0)) type') evalEnv
      pure (RunResult syntax quotedType result, holes)

main :: IO ()
main = do
  let test = runTest run
      testErr = runTestErr run

  putStrLn "=== Universe Polymorphism ==="
  putStrLn ""

  -- Dependent identity
  section "Dependent Functions"
  test
    "dependent id applied to Bool"
    ( Ap
        ( Ap
            ( Anno
                (Pi "a" (Univ (LNat 0)) (FuncTy (Var "a") (Var "a")))
                (Lam "a" (Lam "x" (Var "x")))
            )
            BoolTy
        )
        (Anno BoolTy Tru)
    )
  test
    "dependent id applied to Unit"
    ( Ap
        ( Ap
            ( Anno
                (Pi "a" (Univ (LNat 0)) (FuncTy (Var "a") (Var "a")))
                (Lam "a" (Lam "x" (Var "x")))
            )
            UnitTy
        )
        Unit
    )
  test
    "dependent id unapplied"
    ( Anno
        (Pi "a" (Univ (LNat 0)) (FuncTy (Var "a") (Var "a")))
        (Lam "a" (Lam "x" (Var "x")))
    )
  putStrLn ""

  -- Dependent const
  section "Dependent Const"
  test
    "dependent const applied to Bool and Unit"
    ( Ap
        ( Ap
            ( Ap
                ( Ap
                    ( Anno
                        (Pi "a" (Univ (LNat 0)) (Pi "b" (Univ (LNat 0)) (FuncTy (Var "a") (FuncTy (Var "b") (Var "a")))))
                        (Lam "a" (Lam "b" (Lam "x" (Lam "y" (Var "x")))))
                    )
                    BoolTy
                )
                UnitTy
            )
            (Anno BoolTy Tru)
        )
        Unit
    )
  putStrLn ""

  -- Dependent apply
  section "Dependent Apply"
  test
    "dependent apply with not"
    ( Ap
        ( Ap
            ( Ap
                ( Ap
                    ( Anno
                        (Pi "a" (Univ (LNat 0)) (Pi "b" (Univ (LNat 0)) (FuncTy (FuncTy (Var "a") (Var "b")) (FuncTy (Var "a") (Var "b")))))
                        (Lam "a" (Lam "b" (Lam "f" (Lam "x" (Ap (Var "f") (Var "x"))))))
                    )
                    BoolTy
                )
                BoolTy
            )
            (Anno (FuncTy BoolTy BoolTy) (Lam "x" (If (Var "x") Fls Tru)))
        )
        (Anno BoolTy Tru)
    )
  putStrLn ""

  -- Basic types
  section "Basic Types"
  test
    "Bool is a type"
    (Anno (Univ (LNat 0)) BoolTy)
  test
    "Unit is a type"
    (Anno (Univ (LNat 0)) UnitTy)
  test
    "function type is a type"
    (Anno (Univ (LNat 0)) (FuncTy BoolTy BoolTy))
  test
    "Pi type is a type"
    (Anno (Univ (LNat 1)) (Pi "a" (Univ (LNat 0)) (FuncTy (Var "a") (Var "a"))))
  putStrLn ""

  -- ADTs
  section "ADTs - Maybe"
  test
    "Nothing at Maybe Bool"
    (Anno (AdtTy "Maybe" [BoolTy]) (Cnstr "Nothing" []))
  test
    "Just True at Maybe Bool"
    (Anno (AdtTy "Maybe" [BoolTy]) (Cnstr "Just" [Tru]))
  test
    "Just unit at Maybe Unit"
    (Anno (AdtTy "Maybe" [UnitTy]) (Cnstr "Just" [Unit]))
  putStrLn ""

  section "ADTs - List"
  test
    "Nil at List Bool"
    (Anno (AdtTy "List" [BoolTy]) (Cnstr "Nil" []))
  test
    "singleton list"
    ( Anno
        (AdtTy "List" [BoolTy])
        (Cnstr "Cons" [Tru, Cnstr "Nil" []])
    )
  test
    "two-element list"
    ( Anno
        (AdtTy "List" [BoolTy])
        (Cnstr "Cons" [Fls, Cnstr "Cons" [Tru, Cnstr "Nil" []]])
    )
  putStrLn ""

  section "ADTs - Case"
  test
    "case on Just"
    ( Anno
        BoolTy
        ( Case
            (Anno (AdtTy "Maybe" [BoolTy]) (Cnstr "Just" [Tru]))
            [ ("Nothing", [], Fls),
              ("Just", ["x"], Var "x")
            ]
        )
    )
  test
    "case on Nil"
    ( Anno
        BoolTy
        ( Case
            (Anno (AdtTy "List" [BoolTy]) (Cnstr "Nil" []))
            [ ("Nil", [], Tru),
              ("Cons", ["x", "xs"], Var "x")
            ]
        )
    )
  putStrLn ""

  section "ADTs - Partial Application"
  test
    "partially applied Just"
    (Anno (FuncTy BoolTy (AdtTy "Maybe" [BoolTy])) (Cnstr "Just" []))
  test
    "fully unapplied Cons"
    ( Anno
        (FuncTy BoolTy (FuncTy (AdtTy "List" [BoolTy]) (AdtTy "List" [BoolTy])))
        (Cnstr "Cons" [])
    )
  putStrLn ""

  section "ADTs - Errors"
  testErr
    "wrong number of type args"
    (Anno (AdtTy "Maybe" []) (Cnstr "Just" [Tru]))
  testErr
    "constructor arg type mismatch"
    (Anno (AdtTy "Maybe" [BoolTy]) (Cnstr "Just" [Unit]))
  putStrLn ""

  -- Universes
  section "Universes"
  test
    "Type 0 is a type"
    (Anno (Univ (LNat 1)) (Univ (LNat 0)))
  test
    "Sigma type is a type"
    (Anno (Univ (LNat 1)) (Sigma "a" (Univ (LNat 0)) (FuncTy (Var "a") (Var "a"))))
  test
    "nested universes: Type 0 : Type 1 : Type 2"
    (Anno (Univ (LNat 2)) (Univ (LNat 1)))
  test
    "cumulativity: Bool checked against Type 1"
    (Anno (Univ (LNat 1)) BoolTy)
  test
    "cumulativity: Bool checked against Type 2"
    (Anno (Univ (LNat 2)) BoolTy)
  test
    "maxLevel: Pi with domain at Type 1"
    (Anno (Univ (LNat 2)) (Pi "a" (Univ (LNat 1)) (FuncTy (Var "a") (Var "a"))))
  testErr
    "universe level error: Type 1 at Type 0"
    (Anno (Univ (LNat 0)) (Univ (LNat 1)))
  putStrLn ""

  -- Dependent pairs
  section "Dependent Pairs"
  test
    "non-dependent pair"
    ( Anno
        (PairTy BoolTy UnitTy)
        (Pair Tru Unit)
    )
  test
    "dependent pair: (Bool, if fst then Nat else Unit)"
    ( Anno
        (Sigma "b" BoolTy (If (Var "b") NaturalTy UnitTy))
        (Pair Tru (Natural 42))
    )
  test
    "dependent pair: false branch"
    ( Anno
        (Sigma "b" BoolTy (If (Var "b") NaturalTy UnitTy))
        (Pair Fls Unit)
    )
  test
    "fst of non-dependent pair"
    ( Fst
        ( Anno
            (PairTy BoolTy UnitTy)
            (Pair Tru Unit)
        )
    )
  test
    "snd of non-dependent pair"
    ( Snd
        ( Anno
            (PairTy BoolTy UnitTy)
            (Pair Tru Unit)
        )
    )
  putStrLn ""

  -- Type-level computation
  section "Type-Level Computation"
  test
    "type-level if: true branch"
    ( Ap
        ( Ap
            ( Anno
                (Pi "b" BoolTy (FuncTy (If (Var "b") NaturalTy UnitTy) (If (Var "b") NaturalTy UnitTy)))
                (Lam "b" (Lam "x" (Var "x")))
            )
            Tru
        )
        (Anno NaturalTy (Natural 7))
    )
  test
    "type-level if: false branch"
    ( Ap
        ( Ap
            ( Anno
                (Pi "b" BoolTy (FuncTy (If (Var "b") NaturalTy UnitTy) (If (Var "b") NaturalTy UnitTy)))
                (Lam "b" (Lam "x" (Var "x")))
            )
            Fls
        )
        Unit
    )
  putStrLn ""

  -- Let bindings
  section "Let Bindings"
  test
    "let x = True in x"
    (Anno BoolTy (Let "x" (Anno BoolTy Tru) (Var "x")))
  test
    "let id = (\\x. x) in id True"
    ( Anno
        BoolTy
        ( Let
            "id"
            (Anno (FuncTy BoolTy BoolTy) (Lam "x" (Var "x")))
            (Ap (Var "id") Tru)
        )
    )
  putStrLn ""

  -- Pairs (non-dependent)
  section "Pairs"
  test
    "pair of booleans"
    (Anno (PairTy BoolTy BoolTy) (Pair Tru Fls))
  test
    "nested pair"
    ( Anno
        (PairTy BoolTy (PairTy UnitTy BoolTy))
        (Pair Tru (Pair Unit Fls))
    )
  putStrLn ""

  -- Sums
  section "Sum Types"
  test
    "inl into Bool + Unit"
    (Anno (SumTy BoolTy UnitTy) (InL Tru))
  test
    "inr into Bool + Unit"
    (Anno (SumTy BoolTy UnitTy) (InR Unit))
  test
    "case on sum"
    ( Anno
        BoolTy
        ( SumCase
            (Anno (SumTy BoolTy UnitTy) (InL Tru))
            ("x", Var "x")
            ("y", Fls)
        )
    )
  putStrLn ""

  -- Records
  section "Records"
  test
    "record literal"
    ( Anno
        (RecordTy [("x", BoolTy), ("y", UnitTy)])
        (Record [("x", Tru), ("y", Unit)])
    )
  test
    "record projection"
    ( Get
        "x"
        ( Anno
            (RecordTy [("x", BoolTy), ("y", UnitTy)])
            (Record [("x", Tru), ("y", Unit)])
        )
    )
  putStrLn ""

  -- Subtyping
  section "Subtyping"
  test
    "Nat as Int"
    (Anno IntegerTy (Natural 5))
  test
    "Nat as Real"
    (Anno RealTy (Natural 5))
  test
    "Int as Real"
    (Anno RealTy (Integer 42))
  putStrLn ""

  -- Holes
  section "Holes"
  test
    "hole in check position"
    (Anno BoolTy Hole)
  putStrLn ""

  -- Universe polymorphism
  section "Universe Polymorphism"
  test
    "polymorphic identity"
    ( Anno
        (LevelPi "l" (Pi "a" (Univ (LVar "l")) (FuncTy (Var "a") (Var "a"))))
        (LevelLam "l" (Lam "a" (Lam "x" (Var "x"))))
    )
  test
    "poly id applied at level 0 to Bool"
    ( Anno
        BoolTy
        ( Let
            "id"
            ( Anno
                (LevelPi "l" (Pi "a" (Univ (LVar "l")) (FuncTy (Var "a") (Var "a"))))
                (LevelLam "l" (Lam "a" (Lam "x" (Var "x"))))
            )
            (Ap (Ap (LevelAp (Var "id") (LNat 0)) BoolTy) (Anno BoolTy Tru))
        )
    )
  test
    "poly id at level 1 applied to Type 0"
    ( Anno
        (FuncTy (Univ (LNat 0)) (Univ (LNat 0)))
        ( Let
            "id"
            ( Anno
                (LevelPi "l" (Pi "a" (Univ (LVar "l")) (FuncTy (Var "a") (Var "a"))))
                (LevelLam "l" (Lam "a" (Lam "x" (Var "x"))))
            )
            (Ap (LevelAp (Var "id") (LNat 1)) (Univ (LNat 0)))
        )
    )
  testErr
    "forall l. Type l does not fit in Type 0"
    (Anno (Univ (LNat 0)) (LevelPi "l" (Univ (LVar "l"))))
  test
    "forall l. Type l synthesizes"
    (LevelPi "l" (Univ (LVar "l")))
  test
    "nested forall l. forall m."
    (LevelPi "l" (LevelPi "m" (Univ (LMax (LVar "l") (LVar "m")))))
  test
    "level succ in body"
    (LevelPi "l" (Univ (LSucc (LVar "l"))))

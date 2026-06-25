{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- | System F, the polymorphic lambda calculus.
--
-- System F extends our simply typed language with parametric polymorphism.
-- Terms can abstract over types via big lambda (@Λα. e@), and types can contain
-- universally quantified type variables (@∀α. T@).
--
-- The key addition is a three-level type representation mirroring the term
-- representation:
--
-- 1. 'Type': surface types with named variables (@TVar "a"@).
-- 2. 'SType': core types with de Bruijn indices (@STVar (Ix 0)@).
-- 3. 'VType': evaluated types with de Bruijn levels and closures.
--
-- Types get their own semantic domain ('VType') because @∀@ is represented as a
-- closure ('VForall'). This delays type substitution until instantiation, the
-- same trick as term-level closures avoiding substitution into lambda bodies.
-- The evaluator environment ('EvalEnv') carries separate snoc lists for term
-- values and type values, with independent index spaces.
module Main where

--------------------------------------------------------------------------------

import Control.Arrow ((&&&))
import Control.Monad (foldM, forM, unless, when, zipWithM)
import Control.Monad.Except (MonadError (..))
import Control.Monad.Identity
import Control.Monad.Reader (MonadReader (..), asks)
import Control.Monad.Trans.Except (ExceptT (..))
import Control.Monad.Trans.Reader (Reader, ReaderT (..))
import Control.Monad.Trans.Writer.Strict (WriterT (..))
import Control.Monad.Writer.Strict (MonadWriter (..))
import Data.Foldable (find)
import Data.Functor ((<&>))
import Data.Map (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Scientific (Scientific)
import Data.String
import Data.These
import FoundationSuite (CoreVocab (..), foundationSuite)
import PrettyTerm (Prec, appPrec, arrowPrec, arrowSym, atomPrec, bigLambdaSym, forallSym, lamPrec, lambdaSym, parensIf, sumPrec)
import PrettyTerm qualified as PP
import TestHarness (RunResult (..), assertEval, runTests, section, testErr, testOk)
import Utils (SnocList (..), alignWithM, nth)

--------------------------------------------------------------------------------
-- Syntax
--
-- We use a three-level representation:
--
-- 1. 'Term': surface syntax with named variables, what the programmer writes.
-- 2. 'Syntax': core IR with de Bruijn indices, produced by elaboration.
-- 3. 'Value': semantic domain with closures and neutrals, produced by evaluation.
--
-- 'Term' uses named variables ('Name') instead of de Bruijn indices. The
-- typechecker resolves names to indices during elaboration, producing 'Syntax'.
-- This means typechecking and elaboration happen in a single pass.

-- | Surface syntax with named variables. The programmer writes @λx. x@ and
-- elaboration resolves @x@ to the appropriate de Bruijn index.
data Term
  = -- | A variable reference by name. @x@
    Var Name
  | -- | Lambda abstraction. @\x. body@
    Lam Name Term
  | -- | Function application. @f x@
    Ap Term Arg
  | -- | Let binding. @let x = t1 in t2@
    Let Name Term Term
  | -- | A term with a type annotation that we ignore during evaluation. @(t : A)@
    Anno Type Term
  | -- | A missing subterm. Can only appear in check position (where the
    -- expected type is known). In synth position it's an error.
    Hole
  | -- | Type abstraction (big lambda). @Λα. body@. Binds a type variable in the
    -- body. Checked against a @∀@ type.
    TyLam Name Term
  | -- | Type application. @e [T]@. Instantiates a polymorphic term at a
    -- concrete type.
    TyAp Term Type
  | -- | Pair introduction. @(a, b)@
    Pair Term Term
  | -- | First projection of a pair. @fst p@
    Fst Term
  | -- | Second projection of a pair. @snd p@
    Snd Term
  | -- | Boolean true. @true@
    Tru
  | -- | Boolean false. @false@
    Fls
  | -- | Conditional. @if scrut then t else f@
    If Term Term Term
  | -- | The unit value. @()@
    Unit
  | -- | Void elimination. Can produce any type from a value of type 'Void',
    -- since no such value exists.
    Absurd Term
  | -- | Left injection into a sum type.
    InL Term
  | -- | Right injection into a sum type.
    InR Term
  | -- | Binary sum elimination. Binds a variable in each branch.
    SumCase Term (Name, Term) (Name, Term)
  | -- | A natural number literal.
    Natural Integer
  | -- | An integer literal.
    Integer Integer
  | -- | A real number literal.
    Real Scientific
  | -- | A record literal: a list of named fields with values.
    Record [(Name, Term)]
  | -- | Field projection from a record.
    Get Name Term
  | -- | Apply a named data constructor to arguments.
    Cnstr DtCnstrName [Term]
  | -- | Pattern match on a nominal inductive type. Each branch names a
    -- constructor, binds its fields, and provides a body.
    Case Term [(DtCnstrName, [Name], Term)]
  deriving stock (Show, Eq, Ord)

data Arg = TmArg Term | TpArg Type
  deriving stock (Show, Eq, Ord)

prettyArg :: Prec -> Arg -> PP.Doc ann
prettyArg p = \case
  TmArg tm -> prettyTerm p tm
  TpArg ty -> PP.brackets (prettyType lamPrec ty)

prettyTerm :: Prec -> Term -> PP.Doc ann
prettyTerm _ (Var n) = PP.pretty (getName n)
prettyTerm p (Lam n body) =
  parensIf (p > lamPrec) $
    lambdaSym <> PP.pretty (getName n) <> "." PP.<+> prettyTerm lamPrec body
prettyTerm p (Ap f x) =
  parensIf (p > appPrec) $
    prettyTerm appPrec f PP.<+> prettyArg atomPrec x
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
    prettyTerm (lamPrec + 1) e PP.<+> ":" PP.<+> prettyType lamPrec ty
prettyTerm _ Hole = "_"
prettyTerm p (TyLam n body) =
  parensIf (p > lamPrec) $
    bigLambdaSym <> PP.pretty (getName n) <> "." PP.<+> prettyTerm lamPrec body
prettyTerm p (TyAp e ty) =
  parensIf (p > appPrec) $
    prettyTerm appPrec e PP.<+> PP.brackets (prettyType lamPrec ty)
prettyTerm p (Pair a b) =
  parensIf (p > lamPrec) $
    PP.tupled [prettyTerm lamPrec a, prettyTerm lamPrec b]
prettyTerm p (Fst e) =
  parensIf (p > appPrec) $
    "fst" PP.<+> prettyTerm atomPrec e
prettyTerm p (Snd e) =
  parensIf (p > appPrec) $
    "snd" PP.<+> prettyTerm atomPrec e
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
prettyTerm _ Unit = "()"
prettyTerm p (Absurd e) =
  parensIf (p > appPrec) $
    "absurd" PP.<+> prettyTerm atomPrec e
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
prettyTerm _ (Natural n) = PP.pretty n
prettyTerm _ (Integer n) = PP.pretty n
prettyTerm _ (Real n) = PP.pretty (show n)
prettyTerm _ (Record fields) =
  PP.braces $
    PP.sep $
      PP.punctuate PP.comma $
        map (\(n, e) -> PP.pretty (getName n) PP.<+> "=" PP.<+> prettyTerm lamPrec e) fields
prettyTerm p (Get n e) =
  parensIf (p > appPrec) $
    prettyTerm atomPrec e <> "." <> PP.pretty (getName n)
prettyTerm _ (Cnstr n []) = PP.pretty n
prettyTerm p (Cnstr n args) =
  parensIf (p > appPrec) $
    PP.pretty n PP.<+> PP.hsep (map (prettyTerm atomPrec) args)
prettyTerm p (Case scrut branches) =
  parensIf (p > lamPrec) $
    "case"
      PP.<+> prettyTerm lamPrec scrut
      PP.<+> "of"
      PP.<+> PP.sep
        ( PP.punctuate ";" $
            map
              ( \(cn, binds, body) ->
                  PP.pretty cn
                    PP.<+> PP.hsep (map (PP.pretty . getName) binds)
                    PP.<+> arrowSym
                    PP.<+> prettyTerm lamPrec body
              )
              branches
        )

instance PP.Pretty Term where
  pretty = prettyTerm lamPrec

-- | The type language. Functions, pairs, unit, booleans, natural numbers, and
-- record types.
data Type
  = -- | A type variable reference by name. @a@. Elaboration resolves this to a
    -- de Bruijn index ('STVar').
    TVar Name
  | -- | Universal quantification. @∀α. T@. Binds a named type variable in the
    -- body type.
    Forall Name Type
  | -- | Function type. @A -> B@.
    FuncTy Type Type
  | -- | Pair type. @A * B@.
    PairTy Type Type
  | -- | Bool Type. @Bool@.
    BoolTy
  | -- | Unit type. @Unit@.
    UnitTy
  | -- | The empty type. No values inhabit it.
    VoidTy
  | -- | Binary sum: @A + B@.
    SumTy Type Type
  | -- | Natural numbers. @Nat@. Subtype of 'IntegerTy'.
    NaturalTy
  | -- | Integers. @Int@. Subtype of 'RealTy'.
    IntegerTy
  | -- | Real numbers. @Real@. Top of the numeric tower.
    RealTy
  | -- | A record type: a list of named fields with their types.
    RecordTy [(Name, Type)]
  | -- | A nominal inductive type, referenced by name.
    AdtTy TyCnstrName [Type]
  deriving stock (Show, Eq, Ord)

prettyType :: Prec -> Type -> PP.Doc ann
prettyType _ (TVar n) = PP.pretty (getName n)
prettyType p (Forall n ty) =
  parensIf (p > lamPrec) $
    forallSym <> PP.pretty (getName n) <> "." PP.<+> prettyType lamPrec ty
prettyType p (FuncTy a b) =
  parensIf (p > arrowPrec) $
    prettyType (arrowPrec + 1) a PP.<+> arrowSym PP.<+> prettyType arrowPrec b
prettyType p (PairTy a b) =
  parensIf (p > arrowPrec) $
    prettyType (arrowPrec + 1) a PP.<+> "*" PP.<+> prettyType arrowPrec b
prettyType _ BoolTy = "Bool"
prettyType _ UnitTy = "Unit"
prettyType _ VoidTy = "Void"
prettyType p (SumTy a b) =
  parensIf (p > sumPrec) $
    prettyType (sumPrec + 1) a PP.<+> "+" PP.<+> prettyType sumPrec b
prettyType _ NaturalTy = "Nat"
prettyType _ IntegerTy = "Int"
prettyType _ RealTy = "Real"
prettyType _ (RecordTy fields) =
  PP.braces $
    PP.sep $
      PP.punctuate PP.comma $
        map (\(n, ty) -> PP.pretty (getName n) <> ":" PP.<+> prettyType lamPrec ty) fields
prettyType _ (AdtTy n []) = PP.pretty n
prettyType p (AdtTy n tys) =
  parensIf (p > appPrec) $
    PP.pretty n PP.<+> PP.hsep (map (prettyType atomPrec) tys)

instance PP.Pretty Type where
  pretty = prettyType lamPrec

-- | Core IR with de Bruijn indices.
--
-- This is what the evaluator operates on. Elaboration translates 'Term' into
-- 'Syntax', resolving named variables to indices and stripping away
-- annotations.
data Syntax
  = -- | A resolved variable reference by de Bruijn index.
    SVar Ix
  | -- | Lambda abstraction.
    SLam Name Syntax
  | -- | Function application.
    SAp Syntax Syntax
  | -- | A hole carrying the expected type. Evaluates to a
    -- neutral so it propagates through NbE.
    SHole SType
  | -- | Type abstraction. @Λ. body@. The name is kept for readability in output
    -- but has no semantic role.
    STyLam Name Syntax
  | -- | Type application. @e [T]@. Applies a polymorphic term to a core type.
    STyAp Syntax SType
  | -- | Pair introduction.
    SPair Syntax Syntax
  | -- | First projection of a pair.
    SFst Syntax
  | -- | Second projection of a pair.
    SSnd Syntax
  | -- | Boolean true.
    STru
  | -- | Boolean false.
    SFls
  | -- | Conditional. @if scrut then t else f@.
    SIf Syntax SType Syntax Syntax
  | -- | The unit value.
    SUnit
  | -- | Elimination of the empty type. @absurd t@.
    SAbsurd SType Syntax
  | -- | Left injection into a sum type. @inl x@.
    SInL Syntax
  | -- | Right injection into a sum type. @inr x@.
    SInR Syntax
  | -- | Case analysis on a sum type. @case scrut of inl x -> l; inr y -> r@.
    SSumCase Syntax SType Syntax Syntax
  | -- | A natural number literal.
    SNatural Integer
  | -- | An integer literal.
    SInteger Integer
  | -- | A real number literal.
    SReal Scientific
  | -- | Record introduction. A list of named fields.
    SRecord [(Name, Syntax)]
  | -- | Record field projection. @r.field@.
    SGet Name Syntax
  | -- | A data constructor applied to its elaborated arguments.
    SCnstr DtCnstrName [Syntax]
  | -- | Pattern match on a nominal inductive type. Each branch pairs a
    -- constructor name with an elaborated body (a lambda over the constructor's
    -- fields).
    SCase Syntax [(DtCnstrName, Syntax)]
  deriving stock (Show, Eq, Ord)

-- | Core type IR with de Bruijn indices. Produced by 'elaborateType' from
-- surface 'Type'. Parallels the relationship between 'Term' and 'Syntax' for
-- terms.
--
-- Type variables use de Bruijn indices into the type environment, which is
-- separate from the term variable environment. Binding a type variable (via
-- @∀@) does not shift term indices.
data SType
  = -- | A type variable by de Bruijn index into the type env.
    STVar Ix
  | -- | Universal quantification. @∀. T@. Binds one type variable (index 0 in
    -- the body).
    SForall SType
  | -- | Function type. @A -> B@.
    SFuncTy SType SType
  | -- | Pair type. @A * B@.
    SPairTy SType SType
  | -- | Bool type.
    SBoolTy
  | -- | Unit type.
    SUnitTy
  | -- | The empty type.
    SVoidTy
  | -- | Binary sum type. @A + B@.
    SSumTy SType SType
  | -- | Natural number type.
    SNaturalTy
  | -- | Integer type.
    SIntegerTy
  | -- | Real number type.
    SRealTy
  | -- | Record type.
    SRecordTy [(Name, SType)]
  | -- | A nominal inductive type, referenced by name.
    SAdtTy TyCnstrName [SType]
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
  = -- | A stuck computation, a variable applied to arguments that can't reduce.
    -- The 'Type' annotation is needed so quoting knows how to eta-expand (e.g.,
    -- a neutral at function type gets wrapped in a lambda).
    VNeutral VType Neutral
  | -- | A closure: the lambda body paired with its defining environment.
    -- Application triggers beta reduction by extending this environment.
    VLam Name (Closure Value Syntax)
  | -- | A type closure. Instantiating with a 'VType' extends the type env and
    -- evaluates the body. Computationally irrelevant at runtime, but kept so
    -- quoting can produce normal forms that include type abstractions.
    VTyLam Name (Closure VType Syntax)
  | -- | A fully evaluated pair of values.
    VPair Value Value
  | -- | Boolean true.
    VTru
  | -- | Boolean false.
    VFls
  | -- | The unit value.
    VUnit
  | -- | Left injection value.
    VInL Value
  | -- | Right injection value.
    VInR Value
  | -- | A natural number value.
    VNatural Integer
  | -- | An integer value.
    VInteger Integer
  | -- | A real number value.
    VReal Scientific
  | -- | An evaluated record.
    VRecord [(Name, Value)]
  | -- | An evaluated data constructor with its argument values.
    VCnstr DtCnstrName [Value]
  deriving stock (Show, Eq, Ord)

-- | Evaluated types. The semantic domain for 'SType', produced by 'evalType'.
-- Type variables become de Bruijn levels ('VTVar'), and @∀@ becomes a closure
-- ('VForall') that captures the type environment and delays substitution until
-- instantiation.
--
-- This is the same trick as term-level closures: instead of substituting into
-- the body eagerly, we record what type variables should evaluate to and look
-- them up at use sites.
data VType
  = -- | A type variable as a de Bruijn level.
    VTVar Lvl
  | -- | A type-level closure. When instantiated with a 'VType', extends the
    -- captured type env and evaluates the 'SType' body. This is how type
    -- substitution works in NbE: eval once with the argument in scope, rather
    -- than a syntactic substitution pass.
    VForall (Closure VType SType)
  | -- | Evaluated function type.
    VFuncTy VType VType
  | -- | Evaluated pair type.
    VPairTy VType VType
  | -- | Evaluated bool type.
    VBoolTy
  | -- | Evaluated unit type.
    VUnitTy
  | -- | Evaluated void type.
    VVoidTy
  | -- | Evaluated sum type.
    VSumTy VType VType
  | -- | Evaluated natural number type.
    VNaturalTy
  | -- | Evaluated integer type.
    VIntegerTy
  | -- | Evaluated real number type.
    VRealTy
  | -- | Evaluated record type.
    VRecordTy [(Name, VType)]
  | -- | Evaluated nominal inductive type.
    VAdtTy TyCnstrName [VType]
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
newtype Lvl
  = Lvl Int
  deriving newtype (Show, Eq, Ord, Enum)

initLevel :: Lvl
initLevel = Lvl 0

incLevel :: Lvl -> Lvl
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
    VVar Lvl
  | -- | A typed hole. Carries the 'SType' for round-trip
    -- quoting.
    VHole SType
  deriving (Show, Eq, Ord)

-- | A single eliminator in a neutral's spine.
data Frame
  = -- | Term application. Carries the domain type so quoting
    -- can reconstruct the argument's type.
    VApp VType Value
  | -- | Type application. Carries the applied type so quoting can reconstruct
    -- the type argument.
    VTyApp VType
  | VFst
  | VSnd
  | -- | A stuck if-then-else: the condition is neutral, so we can't choose a
    -- branch. Carries the motive type and both branch values.
    VIf VType Value Value
  | -- | A stuck absurd: the scrutinee is neutral at 'VoidTy'.
    VAbsurd VType
  | -- | A stuck case: the scrutinee is neutral.
    VSumCase VType VType VType Value Value
  | -- | A stuck record projection.
    VGet Name
  | -- | A stuck nominal case: the scrutinee is neutral.
    VCase VType [(DtCnstrName, Value)]
  deriving stock (Show, Eq, Ord)

pushFrame :: Neutral -> Frame -> Neutral
pushFrame Neutral {..} frame = Neutral {head = head, spine = Snoc spine frame}

-- | A closure pairing a body with its defining environment.
-- The phantom @var@ parameter tags what the closure binds:
--
-- * @Closure Value Syntax@: a term lambda. Instantiated by
--   extending the term env with a 'Value'.
-- * @Closure VType Syntax@: a type lambda. Instantiated by
--   extending the type env with a 'VType'.
-- * @Closure VType SType@: a @∀@ type. Instantiated by
--   extending the type env with a 'VType'.
--
-- This lets the type system distinguish the three kinds of
-- closures while sharing the same data representation.
data Closure var a = Closure EvalEnv a
  deriving stock (Show, Eq, Ord)

--------------------------------------------------------------------------------
-- ADTs

newtype TyCnstrName = TyCnstrName {getTyCnstrName :: Name}
  deriving newtype (Show, Eq, Ord, IsString)

instance PP.Pretty TyCnstrName where
  pretty = PP.pretty . getName . getTyCnstrName

newtype DtCnstrName = DtCnstrName {getDtCnstrName :: Name}
  deriving newtype (Show, Eq, Ord, IsString)

instance PP.Pretty DtCnstrName where
  pretty = PP.pretty . getName . getDtCnstrName

-- | Surface syntax for Datatype declarations
data DataDecl = DataDecl TyCnstrName [Name] [CnstrDecl]
  deriving stock (Show, Eq, Ord)

-- | Surface syntax for a single data constructor declaration.
data CnstrDecl = CnstrDecl DtCnstrName [Type]
  deriving stock (Show, Eq, Ord)

-- | Core syntax datatype definition. The @Int@ is the type parameter arity.
--
-- For example, the type @data List a = Nil | Cons a (List a)@ becomes:
--
-- > DataTypeSpec "List" 1
-- >   [ Constr "Nil" (SForall (SAdtTy "List" [STVar 0])),
-- >     Constr "Cons"
-- >       (SForall (SFuncTy (STVar 0)
-- >         (SFuncTy (SAdtTy "List" [STVar 0]) (SAdtTy "List" [STVar 0]))))
-- >   ]
data DataTypeSpec = DataTypeSpec TyCnstrName Int [DataConstructorSpec]
  deriving stock (Show, Eq, Ord)

-- | Core syntax for a single data constructor. @cnstrType@ holds the
-- constructor's full type as a polymorphic scheme, quantified over the
-- data type's parameters.
--
-- The @Cons@ constructor of @List a@, taking an @a@ and a recursive
-- @List a@, becomes:
--
-- > Constr "Cons"
-- >   (SForall (SFuncTy (STVar 0)
-- >     (SFuncTy (SAdtTy "List" [STVar 0]) (SAdtTy "List" [STVar 0]))))
data DataConstructorSpec = Constr
  { cnstrName :: DtCnstrName,
    cnstrType :: SType
  }
  deriving stock (Show, Eq, Ord)

-- | The collection of top-level definitions, with name-based indices
-- for resolving references during elaboration.
--
-- @specs@ is the canonical store, keyed by 'Lvl'. @byType@ and @byCnstr@
-- map surface names to levels and exist only so the elaborator can
-- resolve a written name to its definition. @byType@ maps each type to
-- its level and type parameter arity. @byCnstr@ maps each constructor to
-- the level of its owning type.
data AdtIndex = AdtIndex
  { specs :: Map Lvl Def,
    byType :: Map TyCnstrName (Lvl, Int),
    byCnstr :: Map DtCnstrName Lvl
  }
  deriving stock (Show, Eq, Ord)

-- | A single top-level definition: either a datatype ('Data') or a
-- term definition ('Defn') carrying its type and elaborated body.
data Def
  = Data DataTypeSpec
  | Defn Type Syntax
  deriving stock (Show, Eq, Ord)

-- | An index with no definitions, used to bootstrap elaboration of the
-- stock data types.
emptyAdtIndex :: AdtIndex
emptyAdtIndex = AdtIndex mempty mempty mempty

-- | Elaborate a batch of surface data declarations into an 'AdtIndex' in
-- two phases. Phase 1 registers every type header in @byType@ (with its
-- arity) so that constructor bodies may reference any declared type,
-- including forward and self references. Phase 2 elaborates each
-- constructor, binding the type parameters and building its polymorphic
-- type scheme, and records constructors in @byCnstr@. Both phases reject
-- duplicate type and constructor names.
elaborateDefinitions :: [DataDecl] -> TypecheckM AdtIndex
elaborateDefinitions decls = do
  -- Phase 1: Walk the headers
  byType <- foldM insert Map.empty (zip [Lvl 0 ..] decls)

  -- Phase 2: Walk the bodies
  (specs, byCnstr) <-
    local (\env -> env {adtEnv = env.adtEnv {byType}}) $
      foldM elabDecl (Map.empty, Map.empty) (zip [Lvl 0 ..] decls)

  pure $ AdtIndex {..}
  where
    insert :: Map TyCnstrName (Lvl, Int) -> (Lvl, DataDecl) -> TypecheckM (Map TyCnstrName (Lvl, Int))
    insert acc (l, DataDecl tyName tyParams _) =
      case Map.lookup tyName acc of
        Just _ -> throwError (DuplicateTypeName tyName)
        Nothing -> pure (Map.insert tyName (l, length tyParams) acc)

    elabDecl :: (Map Lvl Def, Map DtCnstrName Lvl) -> (Lvl, DataDecl) -> TypecheckM (Map Lvl Def, Map DtCnstrName Lvl)
    elabDecl (specs, byCnstr) (l, DataDecl tyName tyParams cnstrDecls) = do
      dcSpecs <- withTyParams tyParams $ forM cnstrDecls $ \(CnstrDecl dtName argSurfTys) -> do
        args <- traverse elaborateType argSurfTys
        let k = length tyParams
            retParams = fmap (STVar . Ix) (reverse [0 .. k - 1])
            body = foldr SFuncTy (SAdtTy tyName retParams) args
        pure $ Constr dtName (iterate SForall body !! k)

      let def = Data $ DataTypeSpec tyName (length tyParams) dcSpecs
          specs' = Map.insert l def specs

      byCnstr' <-
        foldM
          ( \acc spec ->
              Map.alterF (\case Just _ -> throwError $ DuplicateConstructorName spec.cnstrName; Nothing -> pure $ Just l) spec.cnstrName acc
          )
          byCnstr
          dcSpecs
      pure (specs', byCnstr')

-- | Look up a data type's spec by name. Returns 'Nothing' if the name is
-- unbound or refers to a term definition rather than a data type.
lookupType :: TyCnstrName -> AdtIndex -> Maybe DataTypeSpec
lookupType tyName AdtIndex {..} = do
  (lvl, _) <- Map.lookup tyName byType
  Map.lookup lvl specs >>= \case
    Data dtSpec -> pure dtSpec
    Defn _ _ -> Nothing

-- | Look up a data constructor by name, returning its owning type and
-- spec. Returns 'Nothing' if no data type declares it.
lookupCnstr :: DtCnstrName -> AdtIndex -> Maybe (TyCnstrName, DataConstructorSpec)
lookupCnstr dtName AdtIndex {..} = do
  lvl <- Map.lookup dtName byCnstr
  Map.lookup lvl specs >>= \case
    Data (DataTypeSpec tyName _arity dtSpecs) -> do
      dtSpec <- find (\(Constr dtName' _) -> dtName == dtName') dtSpecs
      pure (tyName, dtSpec)
    Defn _ _ -> Nothing

-- | Look up a constructor by name within a specific data type. Returns
-- 'Nothing' when that type declares no constructor of the name, which is
-- how constructor membership is checked.
lookupCnstrInType :: TyCnstrName -> DtCnstrName -> AdtIndex -> Maybe DataConstructorSpec
lookupCnstrInType tyName dtName adtIndex = do
  (DataTypeSpec _ _arity cnstrs) <- lookupType tyName adtIndex
  find (\(Constr dtName' _) -> dtName == dtName') cnstrs

bootstrapEnv :: TypeCheckEnv
bootstrapEnv = TypeCheckEnv Nil [] 0 Nil [] 0 mempty emptyAdtIndex

-- | We predefine a few ADTs here for demonstration purposes. In a complete
-- language these would be defined using 'data' declarations in a module.
stockADTs :: AdtIndex
stockADTs =
  either (error . show) id $
    fst $
      runTypecheckM
        ( elaborateDefinitions
            [ DataDecl "Maybe" ["a"] [CnstrDecl "Nothing" [], CnstrDecl "Just" [TVar "a"]],
              DataDecl "List" ["a"] [CnstrDecl "Nil" [], CnstrDecl "Cons" [TVar "a", AdtTy "List" [TVar "a"]]],
              DataDecl "Nat" [] [CnstrDecl "Z" [], CnstrDecl "S" [AdtTy "Nat" []]],
              DataDecl "Wrap" [] [CnstrDecl "MkWrap" [Forall "a" (TVar "a" `FuncTy` TVar "a")]],
              DataDecl "Fn" [] [CnstrDecl "MkFn" [BoolTy `FuncTy` BoolTy]],
              DataDecl "Rect" [] [CnstrDecl "Rect" [RecordTy [("x", NaturalTy), ("y", NaturalTy)]]]
            ]
        )
        bootstrapEnv

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
    cellType :: SType,
    cellValue :: Value
  }
  deriving stock (Show, Eq, Ord)

-- | A type variable binding in the context. Tracks the name (for resolution)
-- and the evaluated type value (a fresh 'VTVar' for universally bound type
-- variables).
data TypeCell = TypeCell
  { typeCellName :: Name,
    typeCellValue :: VType
  }
  deriving stock (Show, Eq, Ord)

-- | The typechecker/elaboration context. Tracks term and type variable bindings
-- in separate index spaces.
--
-- Term variables: @localValues@ holds values by de Bruijn index,
-- @localValuesNames@ maps names to 'Cell's for resolution, and
-- @localValuesSize@ tracks the current term binding depth.
--
-- Type variables: @localTypes@ holds evaluated types by de Bruijn index,
-- @localTypesNames@ maps names to 'TypeCell's, and @localTypesSize@ tracks the
-- current type binding depth.
--
-- Binding a type variable does not shift term indices and vice versa, because
-- the two index spaces are independent.
data TypeCheckEnv = TypeCheckEnv
  { localValues :: SnocList Value,
    localValuesNames :: [Cell],
    localValuesSize :: Int,
    localTypes :: SnocList VType,
    localTypesNames :: [TypeCell],
    localTypesSize :: Int,
    -- | Holes encountered during typechecking
    holes :: [SType],
    -- | ADT Spec by Constructor Name
    adtEnv :: AdtIndex
  }
  deriving stock (Show, Eq, Ord)

-- | The evaluator's environment. Carries two independent snoc lists: one for
-- term variable bindings ('Value') and one for type variable bindings
-- ('VType'). The lengths track the current depth in each index space. Used both
-- as the top-level eval environment and captured inside closures.
data EvalEnv = EvalEnv
  { -- | Type variable bindings, indexed by de Bruijn index.
    envTypes :: SnocList VType,
    -- | Current type binding depth.
    envTypesLen :: Int,
    -- | Term variable bindings, indexed by de Bruijn index.
    envValues :: SnocList Value,
    -- | Current term binding depth.
    envValuesLen :: Int,
    envAdtEnv :: AdtIndex
  }
  deriving stock (Show, Eq, Ord)

-- | Project the evaluator environment from the typechecker context. The
-- typechecker carries extra metadata (names, holes, ADT specs) that the
-- evaluator does not need.
toEvalEnv :: TypeCheckEnv -> EvalEnv
toEvalEnv env =
  EvalEnv
    { envTypes = env.localTypes,
      envTypesLen = env.localTypesSize,
      envValues = env.localValues,
      envValuesLen = env.localValuesSize,
      envAdtEnv = env.adtEnv
    }

initEnv :: TypeCheckEnv
initEnv = TypeCheckEnv Nil [] 0 Nil [] 0 mempty stockADTs

extendLocalNames :: TypeCheckEnv -> Cell -> TypeCheckEnv
extendLocalNames e@TypeCheckEnv {localValuesNames} cell = e {localValuesNames = cell : localValuesNames}

extendHoles :: SType -> TypeCheckEnv -> TypeCheckEnv
extendHoles ty e@TypeCheckEnv {holes} = e {holes = ty : holes}

bindCell :: Cell -> TypeCheckEnv -> TypeCheckEnv
bindCell cell@Cell {..} TypeCheckEnv {..} =
  TypeCheckEnv
    { localValues = Snoc localValues cellValue,
      localValuesNames = cell : localValuesNames,
      localValuesSize = localValuesSize + 1,
      localTypes = localTypes,
      localTypesNames = localTypesNames,
      localTypesSize = localTypesSize,
      holes = holes,
      adtEnv = adtEnv
    }

resolveCell :: TypeCheckEnv -> Name -> Maybe Cell
resolveCell TypeCheckEnv {..} bndr = find ((== bndr) . cellName) localValuesNames

-- | Resolve a type variable name to its 'TypeCell' by linear search through the
-- type variable bindings.
resolveTypeCell :: TypeCheckEnv -> Name -> Maybe TypeCell
resolveTypeCell TypeCheckEnv {..} nm =
  find ((== nm) . typeCellName) localTypesNames

-- | Extend the context with a type variable binding. Adds the evaluated type to
-- @localTypes@ and the cell to @localTypesNames@, incrementing
-- @localTypesSize@. Does not affect the term variable bindings.
bindTypeCell :: TypeCell -> TypeCheckEnv -> TypeCheckEnv
bindTypeCell cell@TypeCell {..} TypeCheckEnv {..} =
  TypeCheckEnv
    { localValues = localValues,
      localValuesNames = localValuesNames,
      localValuesSize = localValuesSize,
      localTypes = Snoc localTypes typeCellValue,
      localTypesNames = cell : localTypesNames,
      localTypesSize = localTypesSize + 1,
      holes = holes,
      adtEnv = adtEnv
    }

-- | Run an action with a data type's parameters bound as fresh type
-- variables, in declaration order. Each parameter is added at the current
-- type binding depth so references elaborate to the expected 'STVar'.
withTyParams :: [Name] -> TypecheckM a -> TypecheckM a
withTyParams tyParams = local $ \typeEnv ->
  foldl' bind typeEnv tyParams
  where
    bind acc tyName = bindTypeCell (TypeCell tyName (VTVar (Lvl acc.localTypesSize))) acc

-- | Create a fresh neutral variable at the current depth. Used for lambda-bound
-- variables where we don't know the value.
freshVar :: TypeCheckEnv -> VType -> Value
freshVar TypeCheckEnv {localValuesSize} ty = VNeutral ty $ Neutral (VVar $ Lvl localValuesSize) Nil

-- | Create a fresh cell for a lambda-bound variable. The value is a neutral
-- because we don't know the argument yet.
freshCell :: TypeCheckEnv -> Name -> SType -> Cell
freshCell ctx name sty = Cell name sty (freshVar ctx (runEvalM (evalType sty) (toEvalEnv ctx)))

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
-- synthesized. The subsumption tactic bridges the two directions.
--
-- Each tactic returns the elaborated core IR: 'Check' returns @Type ->
-- TypecheckM Syntax@ and 'Synth' returns @TypecheckM (Type, Syntax)@. This is
-- the "elaboration." Typechecking and translation happen in one pass.

data Error
  = TypeError String
  | UnknownVariable Name
  | UnknownDataConstructor DtCnstrName
  | UnknownDataType TyCnstrName
  | ConstructorTypeMismatch DtCnstrName TyCnstrName TyCnstrName
  | DuplicateTypeName TyCnstrName
  | DuplicateConstructorName DtCnstrName
  | DataTypeArityMismatch TyCnstrName Int Int
  deriving (Show)

-- | Accumulated hole types from typechecking. Each time the typechecker
-- encounters a 'Hole' in check position, it 'tell's the expected type here.
newtype Holes = Holes {getHoles :: [SType]}
  deriving newtype (Show, Semigroup, Monoid)

newtype TypecheckM a = TypecheckM {runTypecheckM :: TypeCheckEnv -> (Either Error a, Holes)}
  deriving
    (Functor, Applicative, Monad, MonadReader TypeCheckEnv, MonadError Error, MonadWriter Holes)
    via (ExceptT Error (WriterT Holes (Reader TypeCheckEnv)))

newtype Check = Check {runCheck :: SType -> TypecheckM Syntax}

newtype Synth = Synth {runSynth :: TypecheckM (SType, Syntax)}

synth :: Term -> Synth
synth = \case
  Var bndr -> varTactic bndr
  Ap tm arg -> applyTactic (synth tm) arg
  Anno ty tm -> annoTactic ty (check tm)
  Hole -> Synth $ throwError $ TypeError "Cannot sythesize holes"
  TyAp tm ty -> forallElim (synth tm) ty
  Fst tm -> pairElimFst (synth tm)
  Snd tm -> pairElimSnd (synth tm)
  Get name tm -> recordElim name (synth tm)
  tm -> Synth $ throwError $ TypeError $ "Cannot synthesize type for " <> show tm

check :: Term -> Check
check (Lam bndr body) = lamIntro bndr (check body)
check (Let bndr e body) = letTactic bndr (synth e) (check body)
check Hole = holeTactic
check (TyLam bndr body) = forallIntro bndr (check body)
check (Pair tm1 tm2) = pairIntro (check tm1) (check tm2)
check Tru = boolIntroTrue
check Fls = boolIntroFalse
check (If tm1 tm2 tm3) = boolElim (check tm1) (check tm2) (check tm3)
check Unit = unitIntro
check (Absurd tm) = voidElim (synth tm)
check (InL tm1) = sumIntroL (check tm1)
check (InR tm2) = sumIntroR (check tm2)
check (SumCase scrut (bndr1, t1) (bndr2, t2)) = sumElim (synth scrut) (check (Lam bndr1 t1)) (check (Lam bndr2 t2))
check (Natural n) = natIntro n
check (Integer z) = intIntro z
check (Real r) = realIntro r
check (Record fields) = recordIntro (fmap (fmap (id &&& check)) fields)
check (Cnstr nm args) = adtIntro nm (fmap check args)
check (Case scrut cases) = adtElim (synth scrut) (fmap (\(x, y, z) -> (x, check (foldr Lam z y))) cases)
check tm = subTactic (synth tm)

-- | Expose the check goal to a user-space tactic.
--
-- A 'Check' normally consumes its goal inside the newtype. 'matchGoal' unwraps
-- the goal so a user-space tactic can branch on the shape of the expected type,
-- then picks an inner 'Check' and runs it at the same goal.
matchGoal :: (SType -> Check) -> Check
matchGoal tac = Check $ \goal -> runCheck (tac goal) goal

-- | Run a synth tactic once, cache the result, and dispatch.
--
-- 'examine' takes a 'Synth' and a continuation. It runs the tactic exactly once
-- to obtain its synthesized type and elaborated core term, packages that pair
-- into a no-op 'Synth' that replays the cached result, and hands both the
-- cached tactic and the synthesized type to the continuation.
--
-- The continuation can inspect the type, pick a branch, and feed the cached
-- tactic to whichever kernel rule fires. The rule runs the cached tactic, which
-- just returns the memoized pair, without re-typechecking the head.
--
-- Without this caching, a dispatch tactic that inspects the head type and then
-- runs a branch would re-typecheck the head. For a nested application spine,
-- the re-typechecking is exponential.
examine :: Synth -> (Synth -> SType -> Synth) -> Synth
examine tac k = Synth $ do
  (ty, tm) <- runSynth tac
  let memo = Synth (pure (ty, tm))
  runSynth (k memo ty)

-- | Abort a synth with a type error.
--
-- A named primitive so user-space tactics signal ill-formed terms without
-- reaching into the underlying monad directly.
die :: Error -> Synth
die err = Synth (throwError err)

-- | Var Synth
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
      let cellVType = runEvalM (evalType cellType) (toEvalEnv ctx)
          quoted = flip runEvalM (toEvalEnv ctx) $ quote (Lvl ctx.localValuesSize, Lvl ctx.localTypesSize) cellVType cellValue
      pure (cellType, quoted)
    Nothing -> throwError $ UnknownVariable bndr

-- | Subsumption
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
subTactic :: Synth -> Check
subTactic (Synth synth) = Check $ \ty1 -> do
  (ty2, tm) <- synth
  if ty2 `isSubtypeOf` ty1
    then pure tm
    else throwError $ TypeError $ "Type '" <> show ty2 <> "' cannot be a subtype of type '" <> show ty1 <> "'"

-- | Annotation
--
-- The annotation provides a type, switching from synth to check mode. We check
-- the body against the annotated type, then synthesize that type as the result.
-- The annotation itself is erased during elaboration, it doesn't appear in the
-- core 'Syntax'.
--
--    Γ ⊢ e ⇐ A
-- ─────────────── Anno⇒
-- Γ ⊢ (e : A) ⇒ A
annoTactic :: Type -> Check -> Synth
annoTactic ty (Check check) = Synth $ do
  sty <- elaborateType ty
  tm <- check sty
  pure (sty, tm)

-- | Lambda Introduction
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
lamIntro :: Name -> Check -> Check
lamIntro bndr (Check bodyTac) = Check $ \case
  a `SFuncTy` b -> do
    ctx <- ask
    let var = freshCell ctx bndr a
    fiber <- local (bindCell var) $ bodyTac b
    pure $ SLam bndr fiber
  ty -> throwError $ TypeError $ "Tried to introduce a lambda at a non-function type: " <> show ty

-- | Lambda Elimination
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
lamElim :: Synth -> Check -> Synth
lamElim (Synth funcTac) (Check argTac) =
  Synth $
    funcTac >>= \case
      (a `SFuncTy` b, f) -> do
        arg <- argTac a
        pure (b, SAp f arg)
      (ty, _) -> throwError $ TypeError $ "Expected a function type but got " <> show ty

-- | Let Binding
--
-- @let x = e in body@ elaborates to @(λx. body') e'@. There is no dedicated
-- @SLet@ in the core syntax. The let is fully dissolved by NbE: the beta redex
-- reduces and the bound value is inlined into the normal form.
--
-- Unlike 'lamIntro', which binds a fresh neutral variable (since the argument
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
  ctx <- ask
  let val = runEvalM (eval tm1) (toEvalEnv ctx)
      var = Cell bndr ty1 val
  fiber <- local (bindCell var) $ bodyTac ty
  pure $ SAp (SLam bndr fiber) tm1

-- | Hole
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
  tell (Holes [ty])
  pure (SHole ty)

-- | Elaborate a surface 'Type' into a core 'SType'. Resolves named type
-- variables to de Bruijn indices and recurses into composite types. For @TVar@,
-- looks up the name in the type context to find the corresponding level, then
-- converts to an index via 'quoteLevel'. For @Forall@, introduces a fresh type
-- variable and elaborates the body in the extended context.
elaborateType :: Type -> TypecheckM SType
elaborateType = \case
  TVar bndr -> do
    ctx <- ask
    case resolveTypeCell ctx bndr of
      Just TypeCell {..} ->
        case typeCellValue of
          VTVar lvl -> pure $ STVar (quoteLevel (Lvl ctx.localTypesSize) lvl)
          _ -> error "impossible"
      Nothing -> throwError $ UnknownVariable bndr
  Forall nm body -> do
    ctx <- ask
    let tv = VTVar (Lvl ctx.localTypesSize)
        cell = TypeCell nm tv
    body <- local (bindTypeCell cell) $ elaborateType body
    pure $ SForall body
  FuncTy ty1 ty2 -> do
    ty1 <- elaborateType ty1
    ty2 <- elaborateType ty2
    pure $ SFuncTy ty1 ty2
  PairTy ty1 ty2 -> do
    ty1 <- elaborateType ty1
    ty2 <- elaborateType ty2
    pure $ SPairTy ty1 ty2
  BoolTy -> pure SBoolTy
  UnitTy -> pure SUnitTy
  VoidTy -> pure SVoidTy
  SumTy ty1 ty2 -> do
    ty1 <- elaborateType ty1
    ty2 <- elaborateType ty2
    pure $ SSumTy ty1 ty2
  NaturalTy -> pure SNaturalTy
  IntegerTy -> pure SIntegerTy
  RealTy -> pure SRealTy
  RecordTy fields -> do
    fields <- traverse (traverse elaborateType) fields
    pure $ SRecordTy fields
  AdtTy nm tys -> do
    ctx <- ask
    case Map.lookup nm ctx.adtEnv.byType of
      Nothing -> throwError (UnknownDataType nm)
      Just (_lvl, arity) -> do
        unless (length tys == arity) $
          throwError (DataTypeArityMismatch nm arity (length tys))
        tys' <- traverse elaborateType tys
        pure (SAdtTy nm tys')

-- | Forall Introduction
--
--    Γ, α type ⊢ e ⇐ B
--  ─────────────────────── TyLam⇐
--    Γ ⊢ Λα. e ⇐ ∀α. B
forallIntro :: Name -> Check -> Check
forallIntro bndr (Check bodyTac) = Check $ \case
  SForall body -> do
    ctx <- ask
    let tv = VTVar (Lvl ctx.localTypesSize)
        cell = TypeCell bndr tv
    fiber <- local (bindTypeCell cell) $ bodyTac body
    pure $ STyLam bndr fiber
  ty -> throwError $ TypeError $ "Tried to introduce a type lambda at a non-forall type: " <> show ty

-- | Forall Elimination
--
--    Γ ⊢ e ⇒ ∀α. B
--  ────────────────── TyAp⇒
--  Γ ⊢ e [A] ⇒ B[A/α]
forallElim :: Synth -> Type -> Synth
forallElim (Synth synth) surfTy = Synth $ do
  (ty, tm) <- synth
  case ty of
    SForall body -> do
      surfTy <- elaborateType surfTy
      ctx <- ask
      let evalEnv = toEvalEnv ctx
          vArg = runEvalM (evalType surfTy) evalEnv
          extEnv = evalEnv {envTypes = Snoc evalEnv.envTypes vArg, envTypesLen = evalEnv.envTypesLen + 1}
          resultVTy = runEvalM (evalType body) extEnv
          resultSTy = runEvalM (quoteType (Lvl extEnv.envTypesLen) resultVTy) extEnv
      pure (resultSTy, STyAp tm surfTy)
    _ -> throwError $ TypeError $ "Expected a forall type but got " <> show ty

-- | Unified Application
--
-- Dispatches to the appropriate elim rule based on the synthesized type of the
-- head and the shape of the 'Arg'. Uses 'examine' to synthesize the head
-- exactly once, then passes the memoized tactic to whichever branch fires so
-- the kernel rule runs without re-typechecking.
--
-- Four cases. Two dispatch to existing kernel rules, two produce errors for
-- mismatched dispatch, and a fallthrough handles heads whose type is neither a
-- function nor a forall.
--
-- There is no single typing rule for this tactic. It selects between the two
-- underlying rules:
--
-- Γ ⊢ e ⇒ A → B    Γ ⊢ e' ⇐ A
-- ──────────────────────────── App⇒ (term arg)
--   Γ ⊢ Ap e (TmArg e') ⇒ B
--
--       Γ ⊢ e ⇒ ∀α. B
-- ────────────────────────── App⇒ (type arg)
-- Γ ⊢ Ap e (TpArg A) ⇒ B[A/α]
applyTactic :: Synth -> Arg -> Synth
applyTactic t arg = examine t $ \memo tp ->
  case (tp, arg) of
    (SFuncTy _ _, TmArg x) -> lamElim memo (check x)
    (SForall _, TpArg a) -> forallElim memo a
    (SFuncTy _ _, TpArg _) -> die (TypeError "applied a type to a function")
    (SForall _, TmArg _) -> die (TypeError "applied a term to a forall")
    (ty, _) -> die (TypeError ("cannot eliminate " <> show ty))

-- | Pair Introduction
--
-- Like lambdas, pairs are checked. the expected pair type @A × B@ tells us what
-- to check each component against.
--
-- Elaborates to @SPair a' b'@.
--
-- Γ ⊢ a ⇐ A   Γ ⊢ b ⇐ B
-- ───────────────────── Pair⇐
--  Γ ⊢ (a , b) ⇐ A × B
pairIntro :: Check -> Check -> Check
pairIntro (Check checkFst) (Check checkSnd) = Check $ \case
  SPairTy a b -> do
    tm1 <- checkFst a
    tm2 <- checkSnd b
    pure (SPair tm1 tm2)
  ty -> throwError $ TypeError $ "Couldn't match expected type Pair with actual type '" <> show ty <> "'"

-- | Pair Fst Elimination
--
-- Projection is a synth rule. Synthesize the pair's type to learn what the
-- components are, then return the appropriate one.
--
-- Γ ⊢ (t₁ , t₂) ⇒ A × B
-- ───────────────────── Fst⇒
--       Γ ⊢ t₁ ⇒ A
pairElimFst :: Synth -> Synth
pairElimFst (Synth synth) =
  Synth $
    synth >>= \case
      (SPairTy ty1 _ty2, SPair tm1 _tm2) -> pure (ty1, tm1)
      (ty, _) -> throwError $ TypeError $ "Couldn't match expected type Pair with actual type '" <> show ty <> "'"

-- | Pair Snd Elimination
--
-- Same as fst, but returns the second component.
--
-- Γ ⊢ (t₁ , t₂) ⇒ A × B
-- ───────────────────── Snd⇒
--       Γ ⊢ t₂ ⇒ B
pairElimSnd :: Synth -> Synth
pairElimSnd (Synth synth) =
  Synth $
    synth >>= \case
      (SPairTy _ty1 ty2, SPair _tm1 tm2) -> pure (ty2, tm2)
      (ty, _) -> throwError $ TypeError $ "Couldn't match expected type Pair with actual type '" <> show ty <> "'"

-- | Bool True Introduction
--
-- Checked against 'BoolTy' (or a supertype via subtyping).
--
-- ──────────────── True⇐
-- Γ ⊢ True ⇐ Bool
boolIntroTrue :: Check
boolIntroTrue = Check $ \case
  SBoolTy -> pure STru
  ty | SBoolTy `isSubtypeOf` ty -> pure STru
  ty -> throwError $ TypeError $ "'Bool' cannot be a subtype of '" <> show ty <> "'"

-- | Bool False Introduction
--
-- Checked against 'BoolTy'. Elaborates to 'SFls' (or a supertype via subtyping).
--
-- ──────────────── False⇐
-- Γ ⊢ False ⇐ Bool
boolIntroFalse :: Check
boolIntroFalse = Check $ \case
  SBoolTy -> pure SFls
  ty | SBoolTy `isSubtypeOf` ty -> pure SFls
  ty -> throwError $ TypeError $ "'Bool' cannot be a subtype of '" <> show ty <> "'"

-- | Bool Elimination
--
-- Check the condition against 'BoolTy', and both branches against the expected
-- (motive) type. The motive is whatever type the @if@ expression is being
-- checked at. Elaborates to @SIf scrut' t' f'@.
--
-- Γ ⊢ t₁ ⇐ Bool  Γ ⊢ t₂ ⇐ T  Γ ⊢ t₃ ⇐ T
-- ───────────────────────────────────── If⇐
--   Γ ⊢ If t₁ then t₂ else t₃ ⇐ T
boolElim :: Check -> Check -> Check -> Check
boolElim (Check checkT1) (Check checkT2) (Check checkT3) = Check $ \ty -> do
  tm1 <- checkT1 SBoolTy
  tm2 <- checkT2 ty
  tm3 <- checkT3 ty
  pure (SIf tm1 ty tm2 tm3)

-- | Unit Introduction
--
-- Verify the expected type is 'UnitTy' (or a supertype).
--
-- ───────────── Unit⇐
-- Γ ⊢ () ⇐ Unit
unitIntro :: Check
unitIntro = Check $ \case
  SUnitTy -> pure SUnit
  ty | SUnitTy `isSubtypeOf` ty -> pure SUnit
  ty -> throwError $ TypeError $ "'Unit' cannot be a subtype of '" <> show ty <> "'"

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
    SVoidTy -> pure $ SAbsurd ty scrut
    _ -> throwError $ TypeError $ "Expected a Void but got: " <> show scrutTy

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
  SSumTy a _b -> SInL <$> check a
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
  SSumTy _a b -> SInR <$> check b
  ty -> throwError $ TypeError $ "Expected a Sum type but got: " <> show ty

-- | Sum Elimination
--
-- Synthesize the scrutinee's sum type, then check each branch as a
-- function from the injection's payload type to the motive. The
-- branches are elaborated as lambdas that bind the payload.
--
--  Γ ⊢ e ⇒ A + B    Γ ⊢ f ⇐ A → C    Γ ⊢ g ⇐ B → C
--  ─────────────────────────────────────────────── SumCase⇐
--                Γ ⊢ SumCase e f g ⇐ C
sumElim :: Synth -> Check -> Check -> Check
sumElim (Synth synth) (Check checkT1) (Check checkT2) = Check $ \ty -> do
  (scrutTy, scrut) <- synth
  case scrutTy of
    SSumTy a b -> do
      f <- checkT1 (SFuncTy a ty)
      g <- checkT2 (SFuncTy b ty)
      pure $ SSumCase scrut ty f g
    _ -> throwError $ TypeError $ "Expected a Sum type but got: " <> show scrutTy

-- | Natural Introduction
--
-- Checked against 'NaturalTy' (or a supertype via subtyping, e.g. 'IntegerTy'
-- or 'RealTy'). Validates that the literal is non-negative.
--
-- ───────── ℕ⇐
-- Γ ⊢ n ⇐ ℕ
natIntro :: Integer -> Check
natIntro n = Check $ \case
  SNaturalTy ->
    if n >= 0
      then pure (SNatural n)
      else throwError $ TypeError "Naturals must be greater then or equal to zero."
  ty | SNaturalTy `isSubtypeOf` ty -> pure (SNatural n)
  ty -> throwError $ TypeError $ "'Natural' cannot be a subtype of '" <> show ty <> "'"

-- | Integer Introduction
--
-- Checked against 'IntegerTy' (or a supertype via subtyping, e.g. 'RealTy').
--
-- ──────── ℤ⇐
-- Γ ⊢ z ⇐  ℤ
intIntro :: Integer -> Check
intIntro z = Check $ \case
  SIntegerTy -> pure (SInteger z)
  ty | SIntegerTy `isSubtypeOf` ty -> pure (SInteger z)
  ty -> throwError $ TypeError $ "'Integer' cannot be a subtype of '" <> show ty <> "'"

-- | Real Introduction
--
-- Checked against 'RealTy' (or a supertype via subtyping).
--
-- ───────── ℝ⇐
-- Γ ⊢ r ⇐ ℝ
realIntro :: Scientific -> Check
realIntro r = Check $ \case
  SRealTy -> pure (SReal r)
  ty | SRealTy `isSubtypeOf` ty -> pure (SReal r)
  ty -> throwError $ TypeError $ "'Real' cannot be a subtype of '" <> show ty <> "'"

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
  SRecordTy ty -> do
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
      (SRecordTy fields, tm) ->
        case lookup name fields of
          Just ty -> pure (ty, SGet name tm)
          Nothing -> throwError $ TypeError $ "Record does not contain a field called " <> show name
      (ty, _) -> throwError $ TypeError $ "Expected a record type but got " <> show ty

-- | ADT Introduction
--
-- Checked against a type whose return position is an ADT type. The expected
-- type is decomposed by peeling off function arrows until the return type @T ā@
-- is found. The type arguments @ā@ specialize the constructor's polymorphic
-- scheme before its fields are checked.
--
-- Supports partial application via eta expansion. When fewer than @n@ term
-- arguments are provided, the constructor is wrapped in lambdas for all @n@
-- fields and the provided arguments are applied, leaving a function that
-- accepts the remaining fields.
--
-- For example, given @data Maybe a = Nothing | Just a@:
--
-- @(Just True : Maybe Bool)@: the expected type is @Maybe Bool@, so @Just@'s
-- scheme @∀a. a -> Maybe a@ is instantiated at @Bool@ to give @Bool -> Maybe
-- Bool@, and @True@ is checked against @Bool@.
--
-- @(Just : Bool -> Maybe Bool)@: the expected type is @Bool -> Maybe Bool@. The
-- return position is @Maybe Bool@, giving @ā = [Bool]@. No term arguments are
-- provided, so @Just@ is eta-expanded to @λx. Just x@.
--
-- Implementation:
-- 1. Decompose the expected type to find @SAdtTy tyName tys@ at the return
--    position.
-- 2. Look up the constructor spec for @C@, checking that it belongs to
--    @tyName@.
-- 3. Instantiate the constructor's scheme at @tys@ with 'instantiateScheme'
--    and decompose it into its field types.
-- 4. Eta-expand the constructor for all @n@ fields.
-- 5. Check each provided argument against its field type.
-- 6. Apply the checked arguments to the eta-expanded constructor.
--
-- C has fields T₁...Tₙ in spec for T
-- Γ ⊢ tᵢ ⇐ Tᵢ[ā] (i ∈ 1..m, m ≤ n)
-- ──────────────────────────────────────────────── Cnstr⇐
-- Γ ⊢ (λ[x₁...xₙ]. C x₁...xₙ) t₁...tₘ
--   ⇐ Tₘ₊₁[ā] → ... → Tₙ[ā] → T ā
adtIntro :: DtCnstrName -> [Check] -> Check
adtIntro nm chks = Check $ \expectedTy -> do
  let (returnTy, _) = decomposeFunction expectedTy
  case returnTy of
    SAdtTy tyName tys -> do
      adtMap <- asks adtEnv
      case lookupCnstrInType tyName nm adtMap of
        Just dtSpec -> do
          ctx <- ask
          let constrTy = runEvalM (instantiateScheme dtSpec.cnstrType tys) (toEvalEnv ctx)
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
        Nothing ->
          case lookupCnstr nm adtMap of
            Nothing -> throwError $ UnknownDataConstructor nm
            Just (actualTy, _) -> throwError $ ConstructorTypeMismatch nm tyName actualTy
    ty -> throwError $ TypeError $ "Expected an ADT type but got: " <> show ty

-- | Specialize a constructor's polymorphic type scheme to concrete type
-- arguments. Evaluates the scheme to a 'VForall', applies the closure to
-- each type argument in turn, and quotes the result back to an 'SType'.
instantiateScheme :: SType -> [SType] -> EvalM SType
instantiateScheme scheme tys = do
  l <- asks envTypesLen
  vtys <- traverse evalType tys
  vResult <- instantiateSchemeV scheme vtys
  quoteType (Lvl l) vResult

instantiateSchemeV :: SType -> [VType] -> EvalM VType
instantiateSchemeV scheme vtys = do
  vScheme <- evalType scheme
  foldM apply vScheme vtys
  where
    apply :: VType -> VType -> EvalM VType
    apply (VForall body) ty = appTypeClosure body ty
    apply _ _ = error "impossible case: instantiateSchemeV applied a non-forall"

-- | Decompose a function into its return type and a list of its args.
decomposeFunction :: SType -> (SType, [SType])
decomposeFunction (SFuncTy a b) = (a :) <$> decomposeFunction b
decomposeFunction ty = (ty, [])

decomposeVFunc :: VType -> (VType, [VType])
decomposeVFunc (VFuncTy a b) = (a :) <$> decomposeVFunc b
decomposeVFunc ty = (ty, [])

-- | Eta Expand around a data constructor.
etaExpandCnstr :: Int -> Syntax -> Syntax
etaExpandCnstr n t = uncurry ($) $ go n (id, t)
  where
    go 0 (f, t) = (f, t)
    go n (f, SCnstr nm xs) = go (n - 1) (SLam (Name "_") . f, SCnstr nm (xs <> [SVar (Ix $ n - 1)]))
    go _ _ = error "impossible case"

-- | ADT Elimination
--
-- Given an ADT:
--
-- > data List a = Nil | Cons a (List a)
--
-- and a scrutinee of type @List Bool@, we build an eliminator that takes
-- one branch per data constructor and returns a goal type A:
--
-- > list-elim : A -> (Bool -> List Bool -> A) -> List Bool -> A
--
-- NOTE: The Nil branch ought to be @() -> A@ but that is isomorphic to
-- @A@ so we simplify it.
--
-- Each branch is a function from the constructor's fields to A. The field
-- types are the constructor's declared fields instantiated at the
-- scrutinee's type arguments, so for a @List Bool@ scrutinee the type
-- parameter @a@ becomes @Bool@. This is a non-recursive case rather than
-- a fold: a recursive field (the second field of Cons) stays @List Bool@,
-- so the branch receives the substructure itself rather than an already
-- eliminated result. The goal type A is the type of each branch body.
--
-- The core 'DataTypeSpec' for List stores each constructor's full
-- polymorphic type as a scheme:
--
-- > DataTypeSpec "List" 1
-- >   [ Constr "Nil" (SForall (SAdtTy "List" [STVar 0])),
-- >     Constr "Cons"
-- >       (SForall (SFuncTy (STVar 0)
-- >         (SFuncTy (SAdtTy "List" [STVar 0]) (SAdtTy "List" [STVar 0]))))
-- >   ]
--
-- For example:
--
-- > case xs of
-- >   Nil       -> False
-- >   Cons b bs -> b
--
-- with @xs : List Bool@ and goal type Bool checks the Nil body against
-- @Bool@ and the Cons body against @Bool -> List Bool -> Bool@.
adtElim :: Synth -> [(DtCnstrName, Check)] -> Check
adtElim scrut cases = Check $ \motive -> do
  (scrutTy, scrut') <- runSynth scrut
  case scrutTy of
    SAdtTy tyName tys -> do
      ctx <- ask
      case lookupType tyName ctx.adtEnv of
        Just dtSpec -> do
          let branchTys = Map.fromList $ caseBranchTypes (toEvalEnv ctx) motive tys dtSpec
              checks = Map.fromList cases
              alignCases = \case
                These ty chk -> runCheck chk ty
                This _ty -> throwError $ TypeError $ "Missing case for constructor of type '" <> show tyName <> "'"
                That _chk -> throwError $ TypeError $ "Extra case branch not in type '" <> show tyName <> "'"
          cases' <- Map.toList <$> alignWithM alignCases branchTys checks
          pure $ SCase scrut' cases'
        Nothing -> throwError $ UnknownDataType tyName
    ty -> throwError $ TypeError $ "Expected an ADT type but got: " <> show ty

-- | The type a single case branch is checked against: each constructor
-- field becomes a function argument, ending in the goal type.
--
-- The field types come from instantiating the constructor's polymorphic scheme
-- at the scrutinee's type arguments. Recursive fields keep their data type
-- (this is case analysis, not a fold).
constrBranchType :: EvalEnv -> SType -> [SType] -> DataConstructorSpec -> (DtCnstrName, SType)
constrBranchType evalEnv motive tys (Constr nm scheme) =
  let instTy = runEvalM (instantiateScheme scheme tys) evalEnv
      (_ret, fields) = decomposeFunction instTy
   in (nm, foldr SFuncTy motive fields)

-- | The branch types for every constructor of a data type, used to check
-- each arm of a case expression.
caseBranchTypes :: EvalEnv -> SType -> [SType] -> DataTypeSpec -> [(DtCnstrName, SType)]
caseBranchTypes evalEnv motive tys (DataTypeSpec _ _ specs) =
  fmap (constrBranchType evalEnv motive tys) specs

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
isSubtypeOf :: SType -> SType -> Bool
isSubtypeOf s@SFuncTy {} t@SFuncTy {} = functionSubtype s t
isSubtypeOf s@SRecordTy {} t@SRecordTy {} = recordSubtype s t
isSubtypeOf SNaturalTy SIntegerTy = True
isSubtypeOf SNaturalTy SRealTy = True
isSubtypeOf SIntegerTy SRealTy = True
isSubtypeOf super sub = super == sub

-- | Function Subtype
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
functionSubtype :: SType -> SType -> Bool
functionSubtype (s1 `SFuncTy` s2) (t1 `SFuncTy` t2) =
  t1 `isSubtypeOf` s1 && s2 `isSubtypeOf` t2
functionSubtype _ _ = error "impossible case in functionSubtype"

-- | Record Subtyping
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
recordSubtype :: SType -> SType -> Bool
recordSubtype (SRecordTy s) (SRecordTy t) =
  let s' = Map.fromList s
      t' = Map.fromList t
   in Map.isSubmapOfBy (flip isSubtypeOf) t' s'
recordSubtype _ _ = error "impossible case in rec"

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

-- | Evaluate a core 'SType' into 'VType' under the current
-- environment. Type variables are looked up in @envTypes@.
-- @SForall@ captures the current environment in a 'VForall'
-- closure, deferring substitution until the type is
-- instantiated.
evalType :: SType -> EvalM VType
evalType = \case
  STVar (Ix ix) -> do
    env <- asks envTypes
    pure $ fromMaybe (error "internal error") $ nth env ix
  SForall body -> do
    env <- ask
    pure $ VForall $ Closure env body
  SFuncTy t1 t2 -> do
    t1 <- evalType t1
    t2 <- evalType t2
    pure $ VFuncTy t1 t2
  SPairTy t1 t2 -> do
    t1 <- evalType t1
    t2 <- evalType t2
    pure $ VPairTy t1 t2
  SBoolTy -> pure VBoolTy
  SUnitTy -> pure VUnitTy
  SVoidTy -> pure VVoidTy
  SSumTy t1 t2 -> do
    t1 <- evalType t1
    t2 <- evalType t2
    pure $ VSumTy t1 t2
  SNaturalTy -> pure VNaturalTy
  SIntegerTy -> pure VIntegerTy
  SRealTy -> pure VRealTy
  SRecordTy fields -> do
    fields <- forM fields $ \(nm, ty) -> (nm,) <$> evalType ty
    pure $ VRecordTy fields
  SAdtTy nm tys -> do
    tys <- traverse evalType tys
    pure $ VAdtTy nm tys

eval :: Syntax -> EvalM Value
eval = \case
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
    vty <- evalType sty
    pure $ VNeutral vty (Neutral (VHole sty) Nil)
  STyLam bndr body -> do
    env <- ask
    pure $ VTyLam bndr (Closure env body)
  STyAp tm ty -> do
    tm <- eval tm
    ty <- evalType ty
    doTyApply tm ty
  SPair tm1 tm2 -> do
    tm1' <- eval tm1
    tm2' <- eval tm2
    pure $ VPair tm1' tm2'
  SFst tm -> eval tm >>= doFst
  SSnd tm -> eval tm >>= doSnd
  STru -> pure VTru
  SFls -> pure VFls
  SIf p motiv t1 t2 -> do
    p' <- eval p
    t1' <- eval t1
    t2' <- eval t2
    motiv <- evalType motiv
    doIf p' motiv t1' t2'
  SUnit -> pure VUnit
  SAbsurd ty tm -> do
    tm' <- eval tm
    doSumAbsurd tm' ty
  SInL tm -> eval tm <&> VInL
  SInR tm -> eval tm <&> VInR
  SSumCase t1 motive t2 t3 -> do
    t1' <- eval t1
    t2' <- eval t2
    t3' <- eval t3
    doSumCase t1' motive t2' t3'
  SNatural n -> pure $ VNatural n
  SInteger z -> pure $ VInteger z
  SReal r -> pure $ VReal r
  SRecord fields -> doRecord fields
  SGet name tm -> eval tm >>= doGet name
  SCnstr nm bndrs -> doConstructor nm bndrs
  SCase scrut patterns -> doCase scrut patterns

doApply :: Value -> Value -> EvalM Value
doApply (VLam _ clo) arg = appTermClosure clo arg
doApply (VNeutral (VFuncTy ty1 ty2) neu) arg = pure $ VNeutral ty2 (pushFrame neu (VApp ty1 arg))
doApply _ _ = error "impossible case in doApply"

-- | Apply a value to a type argument. If the value is a type
-- lambda, instantiate the closure. If neutral at a @∀@ type,
-- instantiate the 'VForall' closure to compute the result type
-- and push a 'VTyApp' frame onto the spine.
doTyApply :: Value -> VType -> EvalM Value
doTyApply (VTyLam _bndr clo) ty = appTypeTermClosure clo ty
doTyApply (VNeutral (VForall body) neu) ty = do
  clo <- appTypeClosure body ty
  pure $ VNeutral clo (pushFrame neu (VTyApp ty))
doTyApply _ _ = error "impossible case in doTyApply"

doFst :: Value -> EvalM Value
doFst (VPair a _b) = pure a
doFst _ = error "impossible case in doFst"

doSnd :: Value -> EvalM Value
doSnd (VPair _a b) = pure b
doSnd _ = error "impossible case in doSnd"

doSumCase :: Value -> SType -> Value -> Value -> EvalM Value
doSumCase (VInL v) _motive f _ = doApply f v
doSumCase (VInR v) _motive _ g = doApply g v
doSumCase (VNeutral (VSumTy a b) neu) motive f g = do
  motive <- evalType motive
  pure $ VNeutral motive (pushFrame neu (VSumCase (VFuncTy a motive) (VFuncTy b motive) motive f g))
doSumCase _ _ _ _ = error "impossible case in doSumCase"

doSumAbsurd :: Value -> SType -> EvalM Value
doSumAbsurd (VNeutral _ neu) sty = do
  vty <- evalType sty
  pure $ VNeutral vty (pushFrame neu (VAbsurd vty))
doSumAbsurd _ _ = error "impossible case in doSumAbsurd"

doIf :: Value -> VType -> Value -> Value -> EvalM Value
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

doConstructor :: DtCnstrName -> [Syntax] -> EvalM Value
doConstructor nm args = do
  args' <- traverse eval args
  pure $ VCnstr nm args'

doCase :: Syntax -> [(DtCnstrName, Syntax)] -> EvalM Value
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

-- | Instantiate a term closure by extending the term env with a
-- value and evaluating the body. Used for beta reduction at
-- term lambdas.
appTermClosure :: Closure Value Syntax -> Value -> EvalM Value
appTermClosure (Closure env body) v = local (const $ env {envValues = Snoc env.envValues v}) $ eval body

-- | Instantiate a type closure by extending the type env with a
-- type value and evaluating the type body. Used for @∀@
-- instantiation in the type domain.
appTypeClosure :: Closure VType SType -> VType -> EvalM VType
appTypeClosure (Closure env body) v =
  local (const $ env {envTypes = Snoc env.envTypes v, envTypesLen = env.envTypesLen + 1}) $
    evalType body

-- | Instantiate a type-lambda closure by extending the type env
-- with a type value and evaluating the term body. Used for
-- beta reduction at big lambdas (type abstraction applied to a
-- type argument).
appTypeTermClosure :: Closure VType Syntax -> VType -> EvalM Value
appTypeTermClosure (Closure env body) v =
  local (const $ env {envTypes = Snoc env.envTypes v, envTypesLen = env.envTypesLen + 1}) $
    eval body

--------------------------------------------------------------------------------
-- Quoting
--
-- Quoting reads back a 'Value' into 'Syntax' (normal form). It is
-- type-directed: the 'VType' tells us how to handle each value.
--
-- Three key cases dispatch on the type:
--
-- 1. At 'VFuncTy': eta-expand. Generate a fresh variable at the
--    domain type, apply the value to it, quote the result at the
--    codomain. Produces 'SLam'.
-- 2. At 'VForall': eta-expand at the type level. Generate a fresh
--    type variable, type-apply the value to it, instantiate the
--    @∀@ closure to get the result type, quote the result.
--    Produces 'STyLam'.
-- 3. At any other type: the value should be canonical (a pair,
--    constructor, literal, etc.) or neutral. Quote accordingly.
--
-- This ensures normal forms are fully eta-long, so two terms are
-- beta-eta equal iff their normal forms are syntactically
-- identical.
--
-- The @(Lvl, Lvl)@ parameter tracks how many term and type
-- binders we've gone under (independently), so we can convert de
-- Bruijn levels back to indices. Produces 'Syntax' rather than
-- 'Term' since that is what the evaluator and the output both
-- use.

quote :: (Lvl, Lvl) -> VType -> Value -> EvalM Syntax
quote l _ (VNeutral _ neu) = quoteNeutral l neu
quote (l, tl) (VFuncTy ty1 ty2) (VLam bndr clo@(Closure _env _body)) = do
  body <- bindVar ty1 l $ \v l' -> do
    clo <- appTermClosure clo v
    quote (l', tl) ty2 clo
  pure $ SLam bndr body
quote (l, tl) (VFuncTy ty1 ty2) f = do
  body <- bindVar ty1 l $ \v l' ->
    doApply f v >>= quote (l', tl) ty2
  pure $ SLam "_" body
quote (l, tl) (VForall body) (VTyLam bndr clo) = do
  body <- bindTVar tl $ \tv tl -> do
    val <- appTypeTermClosure clo tv
    ty <- appTypeClosure body tv
    quote (l, tl) ty val
  pure $ STyLam bndr body
quote (l, tl) (VForall body) f = do
  body <- bindTVar tl $ \tv tl -> do
    val <- doTyApply f tv
    ty <- appTypeClosure body tv
    quote (l, tl) ty val
  pure $ STyLam "_" body
quote l (VPairTy ty1 ty2) (VPair tm1 tm2) = do
  tm1' <- quote l ty1 tm1
  tm2' <- quote l ty2 tm2
  pure $ SPair tm1' tm2'
quote _ _ VTru = pure STru
quote _ _ VFls = pure SFls
quote _ _ VUnit = pure SUnit
quote l (VSumTy a _b) (VInL tm) = SInL <$> quote l a tm
quote l (VSumTy _a b) (VInR tm) = SInR <$> quote l b tm
quote _ _ (VNatural n) = pure $ SNatural n
quote _ _ (VInteger z) = pure $ SInteger z
quote _ _ (VReal r) = pure $ SReal r
quote l ty (VRecord fields) = SRecord <$> traverse (traverse (quote l ty)) fields
quote l (VAdtTy tyName vtys) (VCnstr nm args) = do
  adtEnv <- asks envAdtEnv
  case lookupCnstrInType tyName nm adtEnv of
    Just (Constr _ scheme) -> do
      instTy <- instantiateSchemeV scheme vtys
      let (_ret, fieldTys) = decomposeVFunc instTy
      SCnstr nm <$> zipWithM (quote l) fieldTys args
    Nothing ->
      error "impossible case in quote: constructor not found in its data type"
quote _ ty tm = error $ "impossible case in quote:\n" <> show ty <> "\n" <> show tm

quoteLevel :: Lvl -> Lvl -> Ix
quoteLevel (Lvl l) (Lvl x) = Ix (l - (x + 1))

quoteNeutral :: (Lvl, Lvl) -> Neutral -> EvalM Syntax
quoteNeutral l Neutral {..} = foldM (quoteFrame l) (quoteHead l head) spine

quoteHead :: (Lvl, Lvl) -> Head -> Syntax
quoteHead (l, _) (VVar lvl) = SVar (quoteLevel l lvl)
quoteHead _ (VHole ty) = SHole ty

quoteFrame :: (Lvl, Lvl) -> Syntax -> Frame -> EvalM Syntax
quoteFrame (l, tl) tm = \case
  VApp ty arg -> SAp tm <$> quote (l, tl) ty arg
  VTyApp ty -> do
    ty <- quoteType tl ty
    pure $ STyAp tm ty
  VFst -> pure $ SFst tm
  VSnd -> pure $ SSnd tm
  VIf ty t1 t2 -> do
    sty <- quoteType tl ty
    liftA2 (SIf tm sty) (quote (l, tl) ty t1) (quote (l, tl) ty t2)
  VAbsurd vty -> do
    sty <- quoteType tl vty
    pure $ SAbsurd sty tm
  VSumCase tyF tyG mot f g -> do
    f' <- quote (l, tl) tyF f
    g' <- quote (l, tl) tyG g
    mot <- quoteType tl mot
    pure $ SSumCase tm mot f' g'
  VGet name -> pure $ SGet name tm
  VCase mot cases -> SCase tm <$> traverse (traverse (quote (l, tl) mot)) cases

-- | Quote an evaluated 'VType' back to core 'SType'. Converts de Bruijn levels
-- back to indices using the provided type binding depth. For 'VForall',
-- introduces a fresh type variable via 'bindTVar', instantiates the closure,
-- and quotes the body at the incremented depth.
quoteType :: Lvl -> VType -> EvalM SType
quoteType l = \case
  VTVar lvl -> do
    pure $ STVar (quoteLevel l lvl)
  VForall body -> do
    body' <- bindTVar l $ \tv l' -> do
      ty <- appTypeClosure body tv
      quoteType l' ty
    pure $ SForall body'
  VFuncTy t1 t2 -> do
    t1 <- quoteType l t1
    t2 <- quoteType l t2
    pure $ SFuncTy t1 t2
  VPairTy t1 t2 -> do
    t1 <- quoteType l t1
    t2 <- quoteType l t2
    pure $ SPairTy t1 t2
  VBoolTy -> pure SBoolTy
  VUnitTy -> pure SUnitTy
  VVoidTy -> pure SVoidTy
  VSumTy t1 t2 -> do
    t1 <- quoteType l t1
    t2 <- quoteType l t2
    pure $ SSumTy t1 t2
  VNaturalTy -> pure SNaturalTy
  VIntegerTy -> pure SIntegerTy
  VRealTy -> pure SRealTy
  VRecordTy fields -> do
    fields <- forM fields (traverse $ quoteType l)
    pure $ SRecordTy fields
  VAdtTy nm tys -> do
    tys <- traverse (quoteType l) tys
    pure $ SAdtTy nm tys

-- | Introduce a fresh term variable at the given level. Creates a neutral value
-- at the given type and passes it (along with the incremented level) to the
-- continuation. Used by quoting to eta-expand at function types.
bindVar :: VType -> Lvl -> (Value -> Lvl -> a) -> a
bindVar ty lvl f =
  let v = VNeutral ty $ Neutral (VVar lvl) Nil
   in f v $ incLevel lvl

-- | Introduce a fresh type variable at the given level. Creates a 'VTVar' and
-- passes it (along with the incremented level) to the continuation. Used by
-- quoting to eta-expand at @∀@ types and by 'quoteType' to go under binders.
bindTVar :: Lvl -> (VType -> Lvl -> a) -> a
bindTVar lvl f =
  let tv = VTVar lvl
   in f tv (incLevel lvl)

--------------------------------------------------------------------------------
-- Main

run :: Term -> Either (Error, Holes) (RunResult Syntax SType Syntax Value, Holes)
run term =
  case runTypecheckM (runSynth $ synth term) initEnv of
    (Left err, holes) -> Left (err, holes)
    (Right (type', syntax), holes) -> do
      let evalEnv = EvalEnv Nil 0 Nil 0 stockADTs
          val = runEvalM (eval syntax) evalEnv
          result = flip runEvalM evalEnv $ do
            type' <- evalType type'
            quote (initLevel, initLevel) type' val
      pure (RunResult syntax type' result val, holes)

-- | This module's mapping of the shared core vocabulary onto its own
-- constructors. Application wraps its argument in 'TmArg' (System F's @Ap@
-- takes a term-or-type 'Arg').
foundationVocab :: CoreVocab Term Type
foundationVocab =
  CoreVocab
    { var = Var . Name,
      lam = Lam . Name,
      ap = \f x -> Ap f (TmArg x),
      let_ = Let . Name,
      anno = Anno,
      hole = Hole,
      pair = Pair,
      fst_ = Fst,
      snd_ = Snd,
      inl = InL,
      inr = InR,
      sumCase = \s (x, l) (y, r) -> SumCase s (Name x, l) (Name y, r),
      absurd = Absurd,
      unit = Unit,
      tru = Tru,
      fls = Fls,
      if_ = If,
      funcTy = FuncTy,
      pairTy = PairTy,
      sumTy = SumTy,
      boolTy = BoolTy,
      unitTy = UnitTy,
      voidTy = VoidTy
    }

main :: IO ()
main = do
  putStrLn "=== System F ==="
  runTests $ do
    -- These foundation tests need unification (metavariable inference): the two
    -- inference lets plus all the holes and unification tests. This module has
    -- no metavariables yet, so they are skipped until it gains unification.
    foundationSuite
      run
      [ "let x = True in (x, x) ==> (True, True)",
        "let f = \\y. y in f () ==> ()",
        "bare _ synthesizes an unsolved metavariable",
        "fst _ : the hole is forced to a pair skeleton",
        "fst (snd _) : nested skeleton",
        "_ () : the hole is forced to a function",
        "(_ () : Unit) pins the hole to Unit -> Unit",
        "case _ of InL/InR : scrutinee hole imitated to a sum",
        "_ (InL True) : domain imitated to a sum",
        "let x = _ in (x, True) : a use solves the hole to Bool",
        "(_, ()) : Bool : a pair cannot unify with Bool",
        "let x = _ in (x, x) : conflicting uses of the same hole",
        "let x = _ in x x : occurs check"
      ]
      foundationVocab

    let test = assertEval run
        smoke = testOk run
        err = testErr run

    -- Polymorphic identity
    section "Type Abstraction & Application"
    test
      "poly id applied to Bool"
      ( Ap
          ( TyAp
              (Anno (Forall "a" (TVar "a" `FuncTy` TVar "a")) (TyLam "a" (Lam "x" (Var "x"))))
              BoolTy
          )
          (TmArg (Anno BoolTy Tru))
      )
      (Anno BoolTy Tru)
    test
      "poly id applied to Unit"
      ( Ap
          ( TyAp
              (Anno (Forall "a" (TVar "a" `FuncTy` TVar "a")) (TyLam "a" (Lam "x" (Var "x"))))
              UnitTy
          )
          (TmArg Unit)
      )
      (Anno UnitTy Unit)
    smoke
      "poly id unapplied"
      ( Anno
          (Forall "a" (TVar "a" `FuncTy` TVar "a"))
          (TyLam "a" (Lam "x" (Var "x")))
      )
    smoke
      "poly id instantiated at Bool"
      ( TyAp
          (Anno (Forall "a" (TVar "a" `FuncTy` TVar "a")) (TyLam "a" (Lam "x" (Var "x"))))
          BoolTy
      )

    -- Polymorphic const
    section "Polymorphic Const"
    test
      "poly const applied to Bool and Unit"
      ( Ap
          ( Ap
              ( TyAp
                  ( TyAp
                      ( Anno
                          (Forall "a" (Forall "b" (TVar "a" `FuncTy` (TVar "b" `FuncTy` TVar "a"))))
                          (TyLam "a" (TyLam "b" (Lam "x" (Lam "y" (Var "x")))))
                      )
                      BoolTy
                  )
                  UnitTy
              )
              (TmArg (Anno BoolTy Tru))
          )
          (TmArg Unit)
      )
      (Anno BoolTy Tru)

    -- Nested forall
    section "Nested Forall"
    test
      "poly apply with not"
      ( Ap
          ( Ap
              ( TyAp
                  ( TyAp
                      ( Anno
                          (Forall "a" (Forall "b" ((TVar "a" `FuncTy` TVar "b") `FuncTy` (TVar "a" `FuncTy` TVar "b"))))
                          (TyLam "a" (TyLam "b" (Lam "f" (Lam "x" (Ap (Var "f") (TmArg (Var "x")))))))
                      )
                      BoolTy
                  )
                  BoolTy
              )
              (TmArg (Anno (BoolTy `FuncTy` BoolTy) (Lam "x" (If (Var "x") Fls Tru))))
          )
          (TmArg (Anno BoolTy Tru))
      )
      (Anno BoolTy Fls)

    -- Impredicative polymorphism
    section "Impredicative Polymorphism"
    smoke
      "impredicative: id applied to id"
      ( Ap
          ( TyAp
              (Anno (Forall "a" (TVar "a" `FuncTy` TVar "a")) (TyLam "a" (Lam "x" (Var "x"))))
              (Forall "b" (TVar "b" `FuncTy` TVar "b"))
          )
          (TmArg (Anno (Forall "b" (TVar "b" `FuncTy` TVar "b")) (TyLam "b" (Lam "x" (Var "x")))))
      )

    -- Error cases
    section "Error Cases (expected failures)"
    err
      "type application of non-forall"
      (TyAp (Anno (BoolTy `FuncTy` BoolTy) (Lam "x" (Var "x"))) BoolTy)
    err
      "type lambda at non-forall type"
      ( Anno
          (BoolTy `FuncTy` BoolTy)
          (TyLam "a" (Lam "x" (Var "x")))
      )
    err
      "unbound type variable"
      ( Anno
          (TVar "a" `FuncTy` TVar "a")
          (Lam "x" (Var "x"))
      )

    -- Polymorphic ADTs
    section "Polymorphic ADTs - Maybe"
    test
      "Nothing at Maybe Bool"
      (Anno (AdtTy "Maybe" [BoolTy]) (Cnstr "Nothing" []))
      (Anno (AdtTy "Maybe" [BoolTy]) (Cnstr "Nothing" []))
    test
      "Just True at Maybe Bool"
      (Anno (AdtTy "Maybe" [BoolTy]) (Cnstr "Just" [Tru]))
      (Anno (AdtTy "Maybe" [BoolTy]) (Cnstr "Just" [Tru]))
    test
      "Just unit at Maybe Unit"
      (Anno (AdtTy "Maybe" [UnitTy]) (Cnstr "Just" [Unit]))
      (Anno (AdtTy "Maybe" [UnitTy]) (Cnstr "Just" [Unit]))

    section "Polymorphic ADTs - List"
    test
      "Nil at List Bool"
      (Anno (AdtTy "List" [BoolTy]) (Cnstr "Nil" []))
      (Anno (AdtTy "List" [BoolTy]) (Cnstr "Nil" []))
    test
      "singleton list"
      ( Anno
          (AdtTy "List" [BoolTy])
          (Cnstr "Cons" [Tru, Cnstr "Nil" []])
      )
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
      ( Anno
          (AdtTy "List" [BoolTy])
          (Cnstr "Cons" [Fls, Cnstr "Cons" [Tru, Cnstr "Nil" []]])
      )

    section "Polymorphic ADTs - Case"
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
      (Anno BoolTy Tru)
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
      (Anno BoolTy Tru)
    test
      "predecessor via case on Nat"
      ( Anno
          (AdtTy "Nat" [])
          ( Case
              (Anno (AdtTy "Nat" []) (Cnstr "S" [Cnstr "S" [Cnstr "Z" []]]))
              [ ("Z", [], Cnstr "Z" []),
                ("S", ["n"], Var "n")
              ]
          )
      )
      (Anno (AdtTy "Nat" []) (Cnstr "S" [Cnstr "Z" []]))

    section "Polymorphic ADTs - Partial Application"
    smoke
      "partially applied Just"
      (Anno (FuncTy BoolTy (AdtTy "Maybe" [BoolTy])) (Cnstr "Just" []))
    smoke
      "fully unapplied Cons"
      ( Anno
          (FuncTy BoolTy (FuncTy (AdtTy "List" [BoolTy]) (AdtTy "List" [BoolTy])))
          (Cnstr "Cons" [])
      )

    section "Polymorphic ADTs - Errors"
    err
      "wrong number of type args"
      (Anno (AdtTy "Maybe" []) (Cnstr "Just" [Tru]))
    err
      "constructor arg type mismatch"
      (Anno (AdtTy "Maybe" [BoolTy]) (Cnstr "Just" [Unit]))
    err
      "Constructor belongs to wrong ADT: Cons checked at Maybe (issue #23)"
      (Anno (AdtTy "Maybe" [BoolTy]) (Cnstr "Cons" [Tru]))
    err
      "Wrong ADT in recursive position: Nothing inside Cons (issue #23)"
      (Anno (AdtTy "List" [BoolTy]) (Cnstr "Cons" [Tru, Cnstr "Nothing" []]))

    section "Function & Higher-Rank Constructor Fields"
    smoke
      "MkFn (\\x. x) at Fn"
      (Anno (AdtTy "Fn" []) (Cnstr "MkFn" [Lam "x" (Var "x")]))
    smoke
      "MkWrap (/\\a. \\x. x) at Wrap"
      (Anno (AdtTy "Wrap" []) (Cnstr "MkWrap" [TyLam "a" (Lam "x" (Var "x"))]))

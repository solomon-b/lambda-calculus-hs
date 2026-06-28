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
import Control.Monad (foldM, forM, replicateM, unless, void, when, zipWithM, zipWithM_, (>=>))
import Control.Monad.Except (MonadError (..))
import Control.Monad.Identity
import Control.Monad.Reader (MonadReader (..), asks)
import Control.Monad.State.Strict (MonadState, StateT (..), gets, modify)
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
-- 3. 'Value': semantic domain with closures and neutrals, produced by
--    evaluation.
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

-- | The type language. Type variables, universal quantification,
-- functions, pairs, sums, unit, booleans, void, the numeric tower
-- (naturals, integers, reals), records, and nominal data types ('AdtTy').
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
    SCase Syntax SType [(DtCnstrName, Syntax)]
  | -- | A reference to a top-level definition, resolved by name in the
    -- global environment. Distinct from 'SVar', which is a local de
    -- Bruijn index.
    SDef Name
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
  | -- | A metavariable: an unknown type, to be solved by unification.
    SMetaTy MetaId
  deriving stock (Show, Eq, Ord)

-- | A metavariable identifier. A metavariable is an unknown type solved
-- by unification. It rides inert through type evaluation as 'VMetaTy',
-- quoted back unchanged, since the evaluator never resolves one. Solving
-- happens only in the typechecker, against the 'MetaCtx' solution map.
newtype MetaId = MetaId Int
  deriving stock (Eq, Ord, Show)

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
  | -- | An unsolved metavariable, carried inert through type evaluation.
    -- 'evalType' produces it from an 'SMetaTy' and 'quoteType' sends it
    -- straight back, since the evaluator never resolves metavariables.
    VMetaTy MetaId
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
  | -- | A stuck nominal case: the scrutinee is neutral. The first 'Type'
    -- is the scrutinee's data type and the second is the result type. Both
    -- are needed to read each branch back at its branch type.
    VCase VType VType [(DtCnstrName, Value)]
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
-- Algebraic Data Types

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

-- | Elaborate one surface data declaration into the 'GlobalIndex'. The
-- type's own header is registered in @byType@ at a fresh level, paired
-- with its parameter arity, so its constructor fields may refer to the
-- type itself (self reference) and to any type declared earlier in the
-- fold. With the type parameters bound as fresh type variables, each
-- constructor's polymorphic scheme is built and recorded in @byCnstr@.
-- Duplicate type names and duplicate constructor names are both rejected.
-- A type declared later in the program is not yet registered, so a
-- forward reference to it fails.
elaborateDataDecl :: GlobalIndex -> DataDecl -> TypecheckM GlobalIndex
elaborateDataDecl idx (DataDecl tyName tyParams cnstrs) = do
  let lvl = nextLvl idx
      arity = length tyParams
  byType' <-
    Map.alterF
      (\case Just _ -> throwError (DuplicateTypeName tyName); Nothing -> pure (Just (lvl, arity)))
      tyName
      (byType idx)

  dcSpecs <-
    local (\env -> env {globals = idx {byType = byType'}}) $ do
      withTyParams tyParams $
        forM cnstrs $ \(CnstrDecl dtName argSurfTys) -> do
          args <- traverse elaborateType argSurfTys
          let retParams = fmap (STVar . Ix) (reverse [0 .. arity - 1])
              body = foldr SFuncTy (SAdtTy tyName retParams) args
          pure $ Constr dtName (iterate SForall body !! arity)

  byCnstr' <-
    foldM
      ( \acc spec ->
          Map.alterF
            (\case Just _ -> throwError (DuplicateConstructorName spec.cnstrName); Nothing -> pure (Just lvl))
            spec.cnstrName
            acc
      )
      (byCnstr idx)
      dcSpecs

  pure
    idx
      { byType = byType',
        specs = Map.insert lvl (Data (DataTypeSpec tyName arity dcSpecs)) (specs idx),
        byCnstr = byCnstr'
      }

-- | Look up a data type's spec by name. Returns 'Nothing' if the name is
-- unbound or refers to a term definition rather than a data type.
lookupType :: TyCnstrName -> GlobalIndex -> Maybe DataTypeSpec
lookupType tyName GlobalIndex {..} = do
  (lvl, _) <- Map.lookup tyName byType
  Map.lookup lvl specs >>= \case
    Data dtSpec -> pure dtSpec
    Defn _ _ -> Nothing

-- | Look up a data constructor by name, returning its owning type and
-- spec. Returns 'Nothing' if no data type declares it.
lookupCnstr :: DtCnstrName -> GlobalIndex -> Maybe (TyCnstrName, DataConstructorSpec)
lookupCnstr dtName GlobalIndex {..} = do
  lvl <- Map.lookup dtName byCnstr
  Map.lookup lvl specs >>= \case
    Data (DataTypeSpec tyName _arity dtSpecs) -> do
      dtSpec <- find (\(Constr dtName' _) -> dtName == dtName') dtSpecs
      pure (tyName, dtSpec)
    Defn _ _ -> Nothing

-- | Look up a constructor by name within a specific data type. Returns
-- 'Nothing' when that type declares no constructor of the name, which is
-- how constructor membership is checked.
lookupCnstrInType :: TyCnstrName -> DtCnstrName -> GlobalIndex -> Maybe DataConstructorSpec
lookupCnstrInType tyName dtName adtIndex = do
  (DataTypeSpec _ _arity cnstrs) <- lookupType tyName adtIndex
  find (\(Constr dtName' _) -> dtName == dtName') cnstrs

-- | We predefine a few ADTs here for demonstration purposes. In a complete
-- language these would be defined using 'data' declarations in a module.
stockADTs :: [DataDecl]
stockADTs =
  [ DataDecl "Maybe" ["a"] [CnstrDecl "Nothing" [], CnstrDecl "Just" [TVar "a"]],
    DataDecl "List" ["a"] [CnstrDecl "Nil" [], CnstrDecl "Cons" [TVar "a", AdtTy "List" [TVar "a"]]],
    DataDecl "Tree" ["a"] [CnstrDecl "Leaf" [TVar "a"], CnstrDecl "Node" [AdtTy "Tree" [TVar "a"], AdtTy "Tree" [TVar "a"]]],
    DataDecl "Nat" [] [CnstrDecl "Z" [], CnstrDecl "S" [AdtTy "Nat" []]],
    DataDecl "Wrap" [] [CnstrDecl "MkWrap" [Forall "a" (TVar "a" `FuncTy` TVar "a")]],
    DataDecl "Fn" [] [CnstrDecl "MkFn" [BoolTy `FuncTy` BoolTy]],
    DataDecl "Rect" [] [CnstrDecl "Rect" [RecordTy [("x", NaturalTy), ("y", NaturalTy)]]]
  ]

--------------------------------------------------------------------------------
-- Top Level Definitions

-- | Surface syntax for a top-level definition: a name, its declared
-- type, and its body.
data DefDecl = DefDecl Name Type Term

-- | Elaborate a list of top-level declarations into the global
-- environment. Each definition is checked and evaluated with the earlier
-- definitions already in scope (the left fold extends @globals@ as it
-- goes), which is how a definition refers to ones declared before it.
elaborateDefDecl :: GlobalIndex -> DefDecl -> TypecheckM GlobalIndex
elaborateDefDecl idx (DefDecl nm ty tm) = do
  local (\env -> env {globals = idx}) $ do
    sty <- elaborateType ty
    syn <- zonkSyntax =<< runCheck (check tm) sty
    evalEnv <- asks toEvalEnv
    let lvl = nextLvl idx
        val = runEvalM (eval syn) evalEnv
    pure
      idx
        { specs = Map.insert lvl (Defn sty val) idx.specs,
          byName = Map.insert nm lvl idx.byName
        }

--------------------------------------------------------------------------------
-- Globals

-- | A single top-level definition: either a datatype ('Data') or a
-- term definition ('Defn') carrying its type and elaborated body.
data Def
  = Data DataTypeSpec
  | Defn SType Value
  deriving stock (Show, Eq, Ord)

bootstrapEnv :: TypeCheckEnv
bootstrapEnv = TypeCheckEnv Nil [] 0 Nil [] 0 [] emptyGlobals

-- | The global environment: every top-level declaration, data type and
-- term definition alike, in one store. @specs@ is the canonical map, keyed
-- by the level a declaration is bound at. The other three are name indices
-- into it, one per namespace. A declaration is reached by looking its name
-- up in the relevant index to get a level, then reading @specs@ there.
data GlobalIndex = GlobalIndex
  { -- | The canonical store, keyed by binding level. 'Data' and 'Defn'
    -- declarations live here together.
    specs :: Map Lvl Def,
    -- | Type namespace: a data type name to its level and arity.
    byType :: Map TyCnstrName (Lvl, Int),
    -- | Constructor namespace: a constructor name to the level of the
    -- data type that declares it.
    byCnstr :: Map DtCnstrName Lvl,
    -- | Term namespace: a top-level definition name to its level.
    byName :: Map Name Lvl
  }
  deriving stock (Show, Eq, Ord)

emptyGlobals :: GlobalIndex
emptyGlobals = GlobalIndex mempty mempty mempty mempty

nextLvl :: GlobalIndex -> Lvl
nextLvl idx = Lvl (Map.size (specs idx))

-- | The predefined top-level definitions available to every program. In
-- a complete language these would be written in source; here they are
-- elaborated once at startup against an empty global environment.
stockDefs :: [DefDecl]
stockDefs =
  [ DefDecl "not" (FuncTy BoolTy BoolTy) (Lam "p" (If (Var "p") Fls Tru)),
    DefDecl "eq" (FuncTy BoolTy (FuncTy BoolTy BoolTy)) (Lam "p" (Lam "q" (If (Var "p") (Var "q") (Ap (Var "not") (TmArg (Var "q")))))),
    DefDecl "and" (FuncTy BoolTy (FuncTy BoolTy BoolTy)) (Lam "p" (Lam "q" (If (Var "p") (Var "q") Fls))),
    DefDecl "or" (FuncTy BoolTy (FuncTy BoolTy BoolTy)) (Lam "p" (Lam "q" (If (Var "p") Tru (Var "q")))),
    DefDecl "nand" (FuncTy BoolTy (FuncTy BoolTy BoolTy)) (Lam "p" (Lam "q" (Ap (Var "not") (TmArg (Ap (Ap (Var "and") (TmArg (Var "p"))) (TmArg (Var "q"))))))),
    DefDecl "twice" (FuncTy (FuncTy BoolTy BoolTy) (FuncTy BoolTy BoolTy)) (Lam "f" (Lam "x" (Ap (Var "f") (TmArg (Ap (Var "f") (TmArg (Var "x")))))))
  ]

data Decl = DefDecl' DefDecl | DataDecl' DataDecl

elaborateDecl :: GlobalIndex -> Decl -> TypecheckM GlobalIndex
elaborateDecl idx = \case
  DefDecl' def -> elaborateDefDecl idx def
  DataDecl' def -> elaborateDataDecl idx def

stockGlobals :: GlobalIndex
stockGlobals =
  either (error . show) id $
    fst $
      fst $
        runTypecheckM
          (foldM elaborateDecl emptyGlobals (fmap DataDecl' stockADTs <> fmap DefDecl' stockDefs))
          initMetas
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
    -- | The global environment: data types and term definitions.
    globals :: GlobalIndex
  }
  deriving stock (Show, Eq, Ord)

-- | The evaluator's environment. Carries two independent snoc lists: one for
-- term variable bindings ('Value') and one for type variable bindings
-- ('VType'), plus the global environment for resolving top-level references
-- ('SDef'). The lengths track the current depth in each index space. Used
-- both as the top-level eval environment and captured inside closures.
data EvalEnv = EvalEnv
  { -- | Type variable bindings, indexed by de Bruijn index.
    evalTypes :: SnocList VType,
    -- | Current type binding depth.
    evalTypesLen :: Int,
    -- | Term variable bindings, indexed by de Bruijn index.
    evalValues :: SnocList Value,
    -- | Current term binding depth.
    evalValuesLen :: Int,
    -- | The global environment, for resolving top-level definitions.
    evalGlobals :: GlobalIndex
  }
  deriving stock (Show, Eq, Ord)

-- | Project the evaluator environment from the typechecker context. The
-- typechecker carries extra metadata (names, holes, binding depth) that the
-- evaluator does not need.
toEvalEnv :: TypeCheckEnv -> EvalEnv
toEvalEnv env =
  EvalEnv
    { evalTypes = env.localTypes,
      evalTypesLen = env.localTypesSize,
      evalValues = env.localValues,
      evalValuesLen = env.localValuesSize,
      evalGlobals = env.globals
    }

initEnv :: TypeCheckEnv
initEnv = TypeCheckEnv Nil [] 0 Nil [] 0 mempty stockGlobals

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
      globals = globals
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
      globals = globals
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
-- Unification
--
-- A metavariable is an unknown type, written 'SMetaTy' and carried as an
-- atomic head alongside the other type formers. The evaluator never
-- inspects one, so the whole solving apparatus lives here in the
-- typechecker, in the 'TypecheckM' state.
--
-- The state is the 'MetaCtx': a counter for minting fresh metavariables
-- and a map from each to its solution. 'freshMeta' mints a new unknown,
-- 'force' resolves a head far enough to see whether it is rigid or still
-- a metavariable, 'solveMeta' records a solution after an occurs check,
-- and 'unify' makes two types equal by solving metavariables.
--
-- 'zonk' and 'zonkSyntax' replace every solved metavariable with its
-- solution. They run before anything crosses into the evaluator, which
-- has no access to the solution map.

-- | The unification state: a counter for minting fresh metavariables and
-- a map from each metavariable to its solution.
data MetaCtx = MetaCtx {next :: MetaId, solutions :: Map MetaId SType}

-- | The empty unification state: no metavariables minted, none solved.
initMetas :: MetaCtx
initMetas = MetaCtx (MetaId 0) mempty

-- | The successor metavariable id.
nextMetaId :: MetaId -> MetaId
nextMetaId (MetaId n) = MetaId (n + 1)

-- | Mint a fresh, unsolved metavariable. Bumps the counter and returns
-- the new 'SMetaTy'.
freshMeta :: TypecheckM SType
freshMeta = do
  i <- gets next
  modify (\m -> m {next = nextMetaId m.next})
  pure $ SMetaTy i

-- | Record the solution @meta := ty@, guarded by an occurs check.
--
-- The check forces at every node as it descends, so it catches @meta@
-- hiding behind an already solved metavariable. If @meta@ occurs in @ty@
-- the solution would be infinite (e.g. @?a := ?a -> ?a@), so we reject it
-- with 'InfiniteTypeError'. Otherwise we store the forced @ty@, keeping
-- the map free of stale metavariable heads.
solveMeta :: MetaId -> SType -> TypecheckM ()
solveMeta meta ty = do
  occured <- occurs ty
  if occured
    then throwError $ InfiniteTypeError ty
    else do
      ty' <- force ty
      modify $ \ctx -> ctx {solutions = Map.insert meta ty' ctx.solutions}
  where
    occurs =
      force >=> \case
        SMetaTy m -> pure (m == meta)
        SFuncTy a b -> (||) <$> occurs a <*> occurs b
        SForall ty -> occurs ty
        SPairTy a b -> (||) <$> occurs a <*> occurs b
        SSumTy a b -> (||) <$> occurs a <*> occurs b
        SRecordTy fields -> or <$> traverse (occurs . snd) fields
        SAdtTy _nm args -> or <$> traverse occurs args
        _ -> pure False

-- | Resolve a type's head. A solved metavariable is chased to its
-- solution (and on, until the head is rigid or unsolved); anything else
-- is returned unchanged. This is shallow: it resolves only the head, not
-- the interior, which is all a consumer needs to tell whether the head is
-- rigid or flexible. Termination relies on the solution map being
-- acyclic, which the occurs check in 'solveMeta' guarantees.
force :: SType -> TypecheckM SType
force = \case
  SMetaTy m ->
    gets (Map.lookup m . solutions) >>= \case
      Just ty -> force ty
      Nothing -> pure (SMetaTy m)
  ty -> pure ty

-- | Resolve every metavariable in a type, head and interior alike. The
-- deep counterpart of 'force', used for display and before a type crosses
-- into the evaluator. A metavariable that survives a zonk is genuinely
-- unsolved and is shown as @?n@.
zonk :: SType -> TypecheckM SType
zonk =
  force >=> \case
    SFuncTy a b -> SFuncTy <$> zonk a <*> zonk b
    SForall ty -> SForall <$> zonk ty
    SPairTy a b -> SPairTy <$> zonk a <*> zonk b
    SSumTy a b -> SSumTy <$> zonk a <*> zonk b
    SRecordTy fields -> SRecordTy <$> traverse (traverse zonk) fields
    SAdtTy nm args -> SAdtTy nm <$> traverse zonk args
    ty -> pure ty

-- | Resolve every metavariable embedded in an elaborated term. The core
-- 'Syntax' carries types: the type of each hole and the motive of each
-- eliminator. The evaluator cannot resolve a metavariable, so the term is
-- zonked before evaluation. The traversal recurses through the whole
-- tree, zonking each embedded type and leaving the term structure intact.
zonkSyntax :: Syntax -> TypecheckM Syntax
zonkSyntax = \case
  SLam nm bdy -> SLam nm <$> zonkSyntax bdy
  SAp f a -> SAp <$> zonkSyntax f <*> zonkSyntax a
  SHole ty -> SHole <$> zonk ty
  SPair a b -> SPair <$> zonkSyntax a <*> zonkSyntax b
  SFst tm -> SFst <$> zonkSyntax tm
  SSnd tm -> SSnd <$> zonkSyntax tm
  SIf s ty t f -> SIf <$> zonkSyntax s <*> zonk ty <*> zonkSyntax t <*> zonkSyntax f
  SAbsurd ty tm -> SAbsurd <$> zonk ty <*> zonkSyntax tm
  SInL tm -> SInL <$> zonkSyntax tm
  SInR tm -> SInR <$> zonkSyntax tm
  SSumCase scrut ty f g -> SSumCase <$> zonkSyntax scrut <*> zonk ty <*> zonkSyntax f <*> zonkSyntax g
  SCnstr nm cnstrs -> SCnstr nm <$> traverse zonkSyntax cnstrs
  SCase scrut ty branches -> SCase <$> zonkSyntax scrut <*> zonk ty <*> traverse (traverse zonkSyntax) branches
  syn -> pure syn

-- | Make two types equal by solving metavariables.
--
-- Both heads are forced first. Two identical metavariables are already
-- equal. A flexible head (an unsolved metavariable) is solved to the
-- other side. Two rigid heads of the same former are decomposed and
-- unified componentwise. Anything else is a rigid mismatch. This is first
-- order and syntactic, so it is complete: if a unifier exists, it is
-- found.
unify :: SType -> SType -> TypecheckM ()
unify a b = do
  a' <- force a
  b' <- force b
  case (a', b') of
    (SMetaTy m, SMetaTy n)
      | m == n -> pure ()
      | otherwise -> solveMeta m b'
    (SMetaTy m, _) -> solveMeta m b'
    (_, SMetaTy n) -> solveMeta n a'
    (SFuncTy x1 y1, SFuncTy x2 y2) -> unify x1 x2 >> unify y1 y2
    (SForall b1, SForall b2) -> unify b1 b2
    (SSumTy x1 y1, SSumTy x2 y2) -> unify x1 x2 >> unify y1 y2
    (SPairTy x1 y1, SPairTy x2 y2) -> unify x1 x2 >> unify y1 y2
    (SRecordTy fields1, SRecordTy fields2) ->
      void $
        alignWithM
          (\case These x y -> unify x y; _ -> throwError (UnificationError a' b'))
          (Map.fromList fields1)
          (Map.fromList fields2)
    (SAdtTy n1 t1, SAdtTy n2 t2)
      | n1 == n2 && length t1 == length t2 -> zipWithM_ unify t1 t2
    _
      | a' == b' -> pure ()
      | otherwise -> throwError (UnificationError a' b')

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
  | InfiniteTypeError SType
  | UnificationError SType SType
  deriving (Show)

-- | Accumulated hole types from typechecking. Each time the typechecker
-- encounters a 'Hole' in check position, it 'tell's the expected type here.
newtype Holes = Holes {getHoles :: [SType]}
  deriving newtype (Show, Semigroup, Monoid)

newtype TypecheckM a = TypecheckM {runTypecheckM :: MetaCtx -> TypeCheckEnv -> ((Either Error a, Holes), MetaCtx)}
  deriving
    (Functor, Applicative, Monad, MonadState MetaCtx, MonadReader TypeCheckEnv, MonadError Error, MonadWriter Holes)
    via (ExceptT Error (WriterT Holes (StateT MetaCtx (Reader TypeCheckEnv))))

newtype Check = Check {runCheck :: SType -> TypecheckM Syntax}

newtype Synth = Synth {runSynth :: TypecheckM (SType, Syntax)}

synth :: Term -> Synth
synth = \case
  Var bndr -> varTactic bndr
  Ap tm arg -> applyTactic (synth tm) arg
  Anno ty tm -> annoTactic ty (check tm)
  Hole -> holeSynthTactic
  TyAp tm ty -> forallElim (synth tm) ty
  Fst tm -> pairElimFst (synth tm)
  Snd tm -> pairElimSnd (synth tm)
  Get name tm -> recordElim name (synth tm)
  tm -> Synth $ throwError $ TypeError $ "Cannot synthesize type for " <> show tm

check :: Term -> Check
check (Lam bndr body) = lamIntro bndr (check body)
check (Let bndr e body) = letTactic bndr (check e) (check body)
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
check (Record fields) = recordIntro (fmap (fmap (id &&& check)) fields)
check (Cnstr nm args) = adtIntro nm (fmap check args)
check (Case scrut cases) = adtElim (synth scrut) (fmap (\(x, y, z) -> (x, check (foldr Lam z y))) cases)
check tm = switchTactic (synth tm)

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
    case Map.lookup nm ctx.globals.byType of
      Nothing -> throwError (UnknownDataType nm)
      Just (_lvl, arity) -> do
        unless (length tys == arity) $
          throwError (DataTypeArityMismatch nm arity (length tys))
        tys' <- traverse elaborateType tys
        pure (SAdtTy nm tys')

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
  forcedTy <- force ty
  let memo = Synth (pure (forcedTy, tm))
  runSynth (k memo forcedTy)

-- | Abort a synth with a type error.
--
-- A named primitive so user-space tactics signal ill-formed terms without
-- reaching into the underlying monad directly.
die :: Error -> Synth
die err = Synth (throwError err)

-- | Variable Resolution
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
-- The cell's type is zonked first. Quoting is type directed and runs in the
-- evaluator, which cannot resolve a metavariable, so a binder whose type is a
-- solved metavariable would otherwise crash the quote.
--
-- (x : A) ∈ Γ
-- ─────────── Var⇒
--  Γ ⊢ x ⇒ A
varTactic :: Name -> Synth
varTactic bndr = Synth $ do
  ctx <- ask

  case resolveCell ctx bndr of
    Just Cell {..} -> do
      zonkedCellType <- zonk cellType
      let cellVType = runEvalM (evalType zonkedCellType) (toEvalEnv ctx)
          quoted = flip runEvalM (toEvalEnv ctx) $ quote (Lvl ctx.localValuesSize, Lvl ctx.localTypesSize) cellVType cellValue
      pure (zonkedCellType, quoted)
    Nothing ->
      case Map.lookup bndr ctx.globals.byName of
        Just lvl ->
          case Map.lookup lvl ctx.globals.specs of
            Just (Defn ty _val) -> pure (ty, SDef bndr)
            _ -> throwError $ UnknownVariable bndr
        _ -> throwError $ UnknownVariable bndr

-- | Switch
--
-- The bridge between synth and check. Synthesize a type for the term, then
-- unify it with the expected type, solving metavariables on either side. This
-- is how a synthesizable term (like a variable or annotation) can appear in a
-- checked position. Every term that doesn't have its own check rule falls
-- through to this. It is the canonical place unification fires: a synthesized
-- type meeting an expected one.
--
-- Γ ⊢ e ⇒ A  A ≡ B
-- ──────────────── Switch⇐
--    Γ ⊢ e ⇐ B
switchTactic :: Synth -> Check
switchTactic switchTac = Check $ \ty1 -> do
  (ty2, tm) <- runSynth switchTac
  unify ty2 ty1

  pure tm

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
annoTactic ty termTac = Synth $ do
  sty <- elaborateType ty
  tm <- runCheck termTac sty
  pure (sty, tm)

-- | Lambda Introduction
--
-- A lambda is checked against a function type. The expected type @A₁ → A₂@
-- tells us what type the parameter has (@A₁@), so we extend the context and
-- check the body against the return type (@A₂@). This is why lambdas can't
-- synthesize. Without the expected function type, we wouldn't know @A₁@.
--
-- The expected type is unified with a fresh @?a -> ?b@ rather than matched
-- directly: if it is already a function type this recovers the domain and
-- codomain, and if it is a flexible metavariable, unification solves it to
-- that function shape (imitation).
--
-- Elaborates to @SLam name body'@.
--
--  Γ, x : A₁ ⊢ e ⇐ A₂
-- ──────────────────── LamIntro⇐
-- Γ ⊢ (λx.e) ⇐ A₁ → A₂
lamIntro :: Name -> Check -> Check
lamIntro bndr bodyTac = Check $ \ty -> do
  a <- freshMeta
  b <- freshMeta
  unify ty (SFuncTy a b)
  a' <- force a

  ctx <- ask
  let var = freshCell ctx bndr a'
  fiber <- local (bindCell var) $ runCheck bodyTac b
  pure $ SLam bndr fiber

-- | Lambda Elimination
--
-- Application is a synth rule. Synthesize the function's type, unify it with a
-- fresh @?a -> ?b@, check the argument against @?a@, and return @?b@. The
-- unification recovers the domain and codomain when the function type is
-- known, and solves a flexible head into a function shape when it is a
-- metavariable (imitation). Information flows from the function to the
-- argument.
--
-- Elaborates to @SAp f' arg'@.
--
-- Γ ⊢ e₁ ⇒ A → B  Γ ⊢ e₂ ⇐ A
-- ────────────────────────── LamElim⇒
--       Γ ⊢ e₁ e₂ ⇒ B
lamElim :: Synth -> Check -> Synth
lamElim funcTac argTac = Synth $ do
  (ty, f) <- runSynth funcTac
  a <- freshMeta
  b <- freshMeta
  unify ty (SFuncTy a b)

  arg <- runCheck argTac a
  pure (b, SAp f arg)

-- | Let Binding
--
-- @let x = e in body@ elaborates to @(λx. body') e'@. There is no dedicated
-- @SLet@ in the core syntax. The let is fully dissolved by NbE: the beta redex
-- reduces and the bound value is inlined into the normal form.
--
-- The right hand side is checked against a fresh metavariable rather than
-- synthesized, so check only intro forms like @True@ or @(a, b)@ can be let
-- bound with no annotation. Unification solves the metavariable from how @e@
-- elaborates, recovering the bound type. A synthesizing @e@ still works: it
-- routes through the switch rule and unifies with the metavariable.
--
-- Unlike 'lamIntro', which binds a fresh neutral variable (since the argument
-- is unknown), the let tactic evaluates @e@ and stores the resulting value in
-- the context cell. This means references to @x@ in the body see the actual
-- value during elaboration, not a stuck variable.
--
--  Γ ⊢ e ⇐ ?α    Γ, x : ?α ⊢ body ⇐ B
--  ──────────────────────────────────────── Let⇐
--         Γ ⊢ let x = e in body ⇐ B
letTactic :: Name -> Check -> Check -> Check
letTactic bndr bndrTac bodyTac = Check $ \ty -> do
  ty1 <- freshMeta
  tm1 <- zonkSyntax =<< runCheck bndrTac ty1
  ctx <- ask
  let val = runEvalM (eval tm1) (toEvalEnv ctx)
      var = Cell bndr ty1 val
  fiber <- local (bindCell var) $ runCheck bodyTac ty
  pure $ SAp (SLam bndr fiber) tm1

-- | Type Hole
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
  forcedTy <- force ty
  case forcedTy of
    SForall body -> do
      surfTy <- elaborateType surfTy
      ctx <- ask
      let evalEnv = toEvalEnv ctx
          vArg = runEvalM (evalType surfTy) evalEnv
          extEnv = evalEnv {evalTypes = Snoc evalEnv.evalTypes vArg, evalTypesLen = evalEnv.evalTypesLen + 1}
          resultVTy = runEvalM (evalType body) extEnv
          resultSTy = runEvalM (quoteType (Lvl extEnv.evalTypesLen) resultVTy) extEnv
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
    (SMetaTy _, TmArg x) -> lamElim memo (check x)
    (ty, _) -> die (TypeError ("cannot eliminate " <> show ty))

holeSynthTactic :: Synth
holeSynthTactic = Synth $ do
  m <- freshMeta
  tell (Holes [m])
  pure (m, SHole m)

-- | Pair Introduction
--
-- Like lambdas, pairs are checked. The expected type is unified with a fresh
-- @?a * ?b@: when it is a known pair type this recovers the component types to
-- check against, and when it is a flexible metavariable, unification solves it
-- to a pair shape (imitation).
--
-- Elaborates to @SPair a' b'@.
--
-- Γ ⊢ a ⇐ A   Γ ⊢ b ⇐ B
-- ───────────────────── Pair⇐
--  Γ ⊢ (a , b) ⇐ A × B
pairIntro :: Check -> Check -> Check
pairIntro checkFst checkSnd = Check $ \ty -> do
  a <- freshMeta
  b <- freshMeta
  unify ty (SPairTy a b)

  tm1 <- runCheck checkFst a
  tm2 <- runCheck checkSnd b
  pure (SPair tm1 tm2)

-- | Pair Fst Elimination
--
-- Projection is a synth rule. Synthesize the operand's type and unify it with
-- a fresh @?a * ?b@, then return the first component. When the operand is a
-- hole, the unification solves its metavariable to a pair (imitation), so
-- @fst _@ learns the hole is a pair and reports the skeleton.
--
-- Γ ⊢ (t₁ , t₂) ⇒ A × B
-- ───────────────────── Fst⇒
--       Γ ⊢ t₁ ⇒ A
pairElimFst :: Synth -> Synth
pairElimFst fstTac = Synth $ do
  (ty, tm) <- runSynth fstTac
  a <- freshMeta
  b <- freshMeta
  unify ty (SPairTy a b)

  pure (a, SFst tm)

-- | Pair Snd Elimination
--
-- Same as fst, but returns the second component.
--
-- Γ ⊢ (t₁ , t₂) ⇒ A × B
-- ───────────────────── Snd⇒
--       Γ ⊢ t₂ ⇒ B
pairElimSnd :: Synth -> Synth
pairElimSnd sndTac = Synth $ do
  (ty, tm) <- runSynth sndTac
  a <- freshMeta
  b <- freshMeta
  unify ty (SPairTy a b)

  pure (b, SSnd tm)

-- | Sum Left Introduction
--
-- Checked against a sum type. The expected type is unified with a fresh
-- @?a + ?b@ and the payload is checked against the left component @?a@.
-- Building a left injection says nothing about the right summand, so @?b@
-- is left unsolved.
--
--      Γ ⊢ e ⇐ A
--  ───────────────── InL⇐
--  Γ ⊢ InL e ⇐ A + B
sumIntroL :: Check -> Check
sumIntroL inlTac = Check $ \ty -> do
  a <- freshMeta
  b <- freshMeta
  unify ty (SSumTy a b)

  tm <- runCheck inlTac a
  pure (SInL tm)

-- | Sum Right Introduction
--
-- Checked against a sum type. The expected type is unified with a fresh
-- @?a + ?b@ and the payload is checked against the right component @?b@.
-- Building a right injection says nothing about the left summand, so @?a@
-- is left unsolved.
--
--  Γ ⊢ e ⇐ B
--  ──────────────── InR⇐
--  Γ ⊢ InR e ⇐ A + B
sumIntroR :: Check -> Check
sumIntroR inrTac = Check $ \ty -> do
  a <- freshMeta
  b <- freshMeta
  unify ty (SSumTy a b)

  tm <- runCheck inrTac b
  pure (SInR tm)

-- | Sum Elimination
--
-- Synthesize the scrutinee's type and unify it with a fresh @?a + ?b@,
-- then check each branch as a function from its payload type to the
-- motive. The branches are elaborated as lambdas that bind the payload.
-- When the scrutinee is a hole, the unification solves its metavariable
-- to a sum (imitation), so @case _ of …@ learns the hole is a sum.
--
--  Γ ⊢ e ⇒ A + B    Γ ⊢ f ⇐ A → C    Γ ⊢ g ⇐ B → C
--  ─────────────────────────────────────────────── SumCase⇐
--                Γ ⊢ SumCase e f g ⇐ C
sumElim :: Synth -> Check -> Check -> Check
sumElim scrutTac leftTac rightTac = Check $ \ty -> do
  (scrutTy, scrut) <- runSynth scrutTac
  a <- freshMeta
  b <- freshMeta
  unify scrutTy (SSumTy a b)

  f <- runCheck leftTac (SFuncTy a ty)
  g <- runCheck rightTac (SFuncTy b ty)
  pure $ SSumCase scrut ty f g

-- | Unit Introduction
--
-- Unify the expected type with 'UnitTy'. When the expected type is a
-- flexible metavariable, this solves it to 'UnitTy'.
--
-- ───────────── Unit⇐
-- Γ ⊢ () ⇐ Unit
unitIntro :: Check
unitIntro = Check $ \ty -> unify ty SUnitTy >> pure SUnit

-- | Bool-True Introduction
--
-- Checked against 'BoolTy'.
--
-- ──────────────── True⇐
-- Γ ⊢ True ⇐ Bool
boolIntroTrue :: Check
boolIntroTrue = Check $ \ty -> unify ty SBoolTy >> pure STru

-- | Bool-False Introduction
--
-- Checked against 'BoolTy'. Elaborates to 'SFls'.
--
-- ──────────────── False⇐
-- Γ ⊢ False ⇐ Bool
boolIntroFalse :: Check
boolIntroFalse = Check $ \ty -> unify ty SBoolTy >> pure SFls

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
boolElim pTac tTac fTac = Check $ \ty -> do
  tm1 <- runCheck pTac SBoolTy
  tm2 <- runCheck tTac ty
  tm3 <- runCheck fTac ty
  pure (SIf tm1 ty tm2 tm3)

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
voidElim voidTac = Check $ \ty -> do
  (scrutTy, scrut) <- runSynth voidTac
  unify scrutTy SVoidTy
  pure $ SAbsurd ty scrut

-- | Record Introduction
--
-- Checked against a record type. A template record type is built from the
-- literal's field names with a fresh metavariable per field, and the
-- expected type is unified against it. When the expected type is a known
-- record, unification aligns the two by label and checks that the field
-- sets match (a label on only one side is a mismatch); when it is a
-- flexible metavariable, unification solves it to that record shape
-- (imitation). Each field is then checked against its metavariable. Field
-- order is irrelevant because unification aligns records by label.
--
--         for each i  Γ ⊢ tᵢ ⇐ Tᵢ
-- ─────────────────────────────────────── Record⇐
-- Γ ⊢ { lᵢ = tᵢ} ⇐ { lᵢ : Tᵢ (i ∈ I..n) }
recordIntro :: [(Name, (Term, Check))] -> Check
recordIntro fields = Check $ \ty -> do
  metas <- traverse (\(name, _) -> (name,) <$> freshMeta) fields
  unify ty (SRecordTy metas)
  fields' <- zipWithM (\(name, m) (_, (_, chk)) -> (name,) <$> runCheck chk m) metas fields
  pure (SRecord fields')

-- | Record Elimination
--
-- Synthesize the record's type, then look up the projected field by name. A
-- synth rule because the record's type tells us the field's type.
--
-- Γ ⊢ t₁ ⇒ { lᵢ : Tᵢ (i ∈ I..n) }
-- ─────────────────────────────── Get⇒
--       Γ ⊢ Get lⱼ t₁ ⇒ Tⱼ
recordElim :: Name -> Synth -> Synth
recordElim name fieldTac =
  Synth $
    runSynth fieldTac >>= \(ty, tm) -> do
      force ty >>= \case
        SRecordTy fields ->
          case lookup name fields of
            Just ty -> pure (ty, SGet name tm)
            Nothing -> throwError $ TypeError $ "Record does not contain a field called " <> show name
        ty' -> throwError $ TypeError $ "Expected a record type but got " <> show ty'

-- | ADT Introduction
--
-- Checked against a type whose return position is an ADT type. The
-- constructor's polymorphic scheme is instantiated at a fresh metavariable
-- per type parameter, and its return type @T ?ā@ is unified with the goal's
-- return position. That solves the metavariables, specializing the field
-- types, and also works when the goal is itself a metavariable rather than a
-- concrete @SAdtTy@.
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
-- 1. Look up the constructor spec for @C@ and its owning type @tyName@.
-- 2. Mint a fresh metavariable per type parameter and instantiate the scheme
--    at them with 'instantiateScheme', then decompose into the constructor's
--    return type and field types.
-- 3. Unify that return type with the goal's return position, solving the
--    metavariables.
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
  ctx <- ask
  let (returnTy, _) = decomposeFunction expectedTy
  case lookupCnstr nm ctx.globals of
    Nothing -> throwError (UnknownDataConstructor nm)
    Just (tyName, dtSpec) -> do
      (_, arity) <- maybe (throwError (UnknownDataType tyName)) pure $ Map.lookup tyName ctx.globals.byType
      metas <- replicateM arity freshMeta

      let instTy = runEvalM (instantiateScheme dtSpec.cnstrType metas) (toEvalEnv ctx)
          (cstrReturnTy, paramTys) = decomposeFunction instTy

      unify returnTy cstrReturnTy

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

-- | Specialize a constructor's polymorphic type scheme to concrete type
-- arguments. Evaluates the scheme to a 'VForall', applies the closure to
-- each type argument in turn, and quotes the result back to an 'SType'.
instantiateScheme :: SType -> [SType] -> EvalM SType
instantiateScheme scheme tys = do
  l <- asks evalTypesLen
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
  globals <- asks globals
  (scrutTy, scrut') <- runSynth scrut

  -- Resolve the ADT name. With branches, any constructor names it (they're
  -- globally unique); with none, only the scrutinee can.
  (tyName, args) <- case cases of
    ((cn, _) : _) -> case lookupCnstr cn globals of
      Just (n, _) -> do
        (_, arity) <- maybe (throwError (UnknownDataType n)) pure $ Map.lookup n globals.byType
        metas <- replicateM arity freshMeta
        pure (n, metas)
      Nothing -> throwError (UnknownDataConstructor cn)
    [] ->
      force scrutTy >>= \case
        SAdtTy n args -> pure (n, args)
        other -> throwError $ TypeError $ "Cannot infer ADT for an empty case: " <> show other

  unify scrutTy (SAdtTy tyName args)

  ctx <- ask

  case lookupType tyName globals of
    Just dtSpec -> do
      let branchTypes = Map.fromList $ caseBranchTypes (toEvalEnv ctx) motive args dtSpec
          checks = Map.fromList cases
          alignCases = \case
            These ty chk -> runCheck chk ty
            This _ty -> throwError $ TypeError $ "Missing case for constructor of type '" <> show tyName <> "'"
            That _chk -> throwError $ TypeError $ "Extra case branch not in type '" <> show tyName <> "'"
      cases' <- Map.toList <$> alignWithM alignCases branchTypes checks
      pure $ SCase scrut' motive cases'
    Nothing -> throwError $ UnknownDataType tyName

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
-- environment. Type variables are looked up in @evalTypes@.
-- @SForall@ captures the current environment in a 'VForall'
-- closure, deferring substitution until the type is
-- instantiated.
evalType :: SType -> EvalM VType
evalType = \case
  STVar (Ix ix) -> do
    env <- asks evalTypes
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
  SMetaTy m -> pure $ VMetaTy m

eval :: Syntax -> EvalM Value
eval = \case
  SVar (Ix ix) -> do
    env <- asks evalValues
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
  SCase scrut mot patterns -> do
    mot' <- evalType mot
    doCase scrut mot' patterns
  SDef nm -> do
    globals <- asks evalGlobals
    case Map.lookup nm globals.byName of
      Just lvl ->
        case Map.lookup lvl globals.specs of
          Just (Defn _ value) -> pure value
          _ -> error "internal error: unbound global reference"
      Nothing -> error "internal error: unbound global reference"

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
doFst (VNeutral (VPairTy a _) neu) = pure $ VNeutral a (pushFrame neu VFst)
doFst _ = error "impossible case in doFst"

doSnd :: Value -> EvalM Value
doSnd (VPair _a b) = pure b
doSnd (VNeutral (VPairTy _ b) neu) = pure $ VNeutral b (pushFrame neu VSnd)
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

-- | Evaluate case analysis. The 'Type' is the result type. On a constructor
-- value, select the matching branch and apply it to the constructor's
-- fields. On a neutral scrutinee, build a stuck 'VCase' frame carrying the
-- scrutinee's data type and the result type.
doCase :: Syntax -> VType -> [(DtCnstrName, Syntax)] -> EvalM Value
doCase scrut mot patterns = do
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
      pure $ VNeutral mot (pushFrame neu (VCase ty mot branches))
    _ -> error "impossible case in doCase: non-constructor scrutinee"

-- | Instantiate a term closure by extending the term env with a
-- value and evaluating the body. Used for beta reduction at
-- term lambdas.
appTermClosure :: Closure Value Syntax -> Value -> EvalM Value
appTermClosure (Closure env body) v = local (const $ env {evalValues = Snoc env.evalValues v}) $ eval body

-- | Instantiate a type closure by extending the type env with a
-- type value and evaluating the type body. Used for @∀@
-- instantiation in the type domain.
appTypeClosure :: Closure VType SType -> VType -> EvalM VType
appTypeClosure (Closure env body) v =
  local (const $ env {evalTypes = Snoc env.evalTypes v, evalTypesLen = env.evalTypesLen + 1}) $
    evalType body

-- | Instantiate a type-lambda closure by extending the type env
-- with a type value and evaluating the term body. Used for
-- beta reduction at big lambdas (type abstraction applied to a
-- type argument).
appTypeTermClosure :: Closure VType Syntax -> VType -> EvalM Value
appTypeTermClosure (Closure env body) v =
  local (const $ env {evalTypes = Snoc env.evalTypes v, evalTypesLen = env.evalTypesLen + 1}) $
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
  globals <- asks evalGlobals
  case lookupCnstrInType tyName nm globals of
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
  VCase (VAdtTy scrut args) mot cases -> do
    ctx <- ask
    mot' <- quoteType tl mot
    args' <- traverse (quoteType tl) args
    patterns' <- forM cases $ \(dtName, val) -> do
      case lookupCnstrInType scrut dtName ctx.evalGlobals of
        Just dtSpec -> do
          let (cnstrName, patTy) = constrBranchType ctx mot' args' dtSpec
          patTy' <- evalType patTy
          syn <- quote (l, tl) patTy' val
          pure (cnstrName, syn)
        Nothing ->
          error "impossible case in quote: constructor not found in its data type"
    pure $ SCase tm mot' patterns'
  VCase {} -> error "impossible case in quote: cannot quote VCase against a non AdtTy"

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
  VMetaTy m -> pure $ SMetaTy m

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

run :: Term -> Either (Error, Holes) (RunResult Syntax VType Syntax Value, Holes)
run term =
  let action = do
        ((ty, syn), hs) <- listen (runSynth (synth term))
        ty' <- zonk ty
        hs' <- traverse zonk (getHoles hs)
        zonkedSyn <- zonkSyntax syn
        pure (ty', zonkedSyn, Holes hs')
   in case runTypecheckM action initMetas initEnv of
        ((Left err, holes), _metas) -> Left (err, holes)
        ((Right (type', syntax, holes), _unZonkedHoles), _metas) -> do
          let evalEnv = EvalEnv Nil 0 Nil 0 stockGlobals
              val = runEvalM (eval syntax) evalEnv
              type'' = runEvalM (evalType type') evalEnv
              result = runEvalM (quote (initLevel, initLevel) type'' val) evalEnv
          pure (RunResult syntax type'' result val, holes)

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
      []
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

    -- Metavariable scope. The first-order unifier here solves syntactically,
    -- with no record of where each metavariable was created, so it cannot
    -- tell an in-scope solution from an escaping one. The three cases below
    -- are the acceptance spec for that distinction:
    --
    --   T1  a check-position hole under a binder. No metavariable is solved,
    --       so nothing can escape. Passes here.
    --   T2  a metavariable born inside the Λ, solved to a type variable that
    --       is in scope at its creation. Legitimate. Passes here, though only
    --       by luck: there is no check, the de Bruijn index just lands in
    --       range.
    --   T3  a metavariable born outside the Λ (via the let), then forced to
    --       the inner-bound a. The meta predates the binder, so the solution
    --       escapes. This module cannot reject it: elaboration "succeeds" and
    --       the bound variable leaks to the top level, where evalType hits an
    --       out-of-range index and crashes. T3 is therefore not a live test
    --       below, only T1 and T2 are; its surface term, for the next module
    --       to reject, is:
    --
    --         (let f = _ in /\a. (f : a)) : forall a. a
    --
    --           Anno (Forall "a" (TVar "a"))
    --             (Let "f" Hole (TyLam "a" (Anno (TVar "a") (Var "f"))))
    --
    -- The fix needs each metavariable to remember the scope it was born in,
    -- which is the spine of the next module: DK-style bidirectional inference
    -- over an ordered context, where "solve only using variables to your
    -- left" makes T2 accepted and T3 rejected by construction (and, the
    -- actual prize, lets us infer type applications).
    section "Metavariable Scope"
    -- T1: a check-position hole under a binder. The hole records a -> a
    -- locally and no metavariable is solved, so nothing can escape.
    smoke
      "T1: /\\a. (_ : a -> a) records the hole, no escape"
      (Anno (Forall "a" (FuncTy (TVar "a") (TVar "a"))) (TyLam "a" Hole))
    -- T2: the metavariable is created inside the Λ and solved to a, which is
    -- in scope at its creation. Legitimate; accepted here (see note above).
    smoke
      "T2: /\\a. let h = _ in (h : a) solves in scope"
      ( Anno
          (Forall "a" (TVar "a"))
          (TyLam "a" (Let "h" Hole (Anno (TVar "a") (Var "h"))))
      )

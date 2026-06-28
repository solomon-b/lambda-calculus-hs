{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- | Martin-Löf Type Theory with @Type : Type@.
--
-- Extends the simply typed core with dependent types. The key change
-- from System F is that types and terms share a single syntax,
-- core IR, and semantic domain. Pi and Sigma types bind a variable
-- whose type can appear in the body, collapsing the former
-- term/type separation. Non-dependent functions (@A -> B@) and
-- pairs (@A * B@) are kept as separate constructors alongside Pi
-- and Sigma rather than being desugared. This keeps the elaboration
-- rules for the simply typed fragment unchanged and lets the pretty
-- printer recover the non-dependent surface syntax without
-- inspecting binder occurrences.
--
-- The universe is inconsistent (@Type : Type@) for simplicity.
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
import Data.Foldable (find, foldrM)
import Data.Functor ((<&>))
import Data.Map (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Scientific (Scientific)
import Data.String
import Data.These
import FoundationSuite (CoreVocab (..), foundationSuite)
import PrettyTerm (Prec, appPrec, arrowPrec, arrowSym, atomPrec, lamPrec, lambdaSym, parensIf, sumPrec)
import PrettyTerm qualified as PP
import TestHarness (RunResult (..), assertEval, runTests, section, testErr, testOk)
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
  | -- | The universe of types. @Type : Type@ (inconsistent
    -- but simple).
    Univ
  | -- | Dependent function type. @(x : A) -> B@. Binds a
    -- variable in the codomain. Non-dependent functions use
    -- 'FuncTy' as sugar.
    Pi Name Term Term
  | -- | Non-dependent function type. @A -> B@.
    FuncTy Term Term
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
    AdtTy TyCnstrName [Term]
  | -- | Apply a named data constructor to arguments.
    Cnstr DtCnstrName [Term]
  | -- | Pattern match on a nominal inductive type. Each
    -- branch names a constructor, binds its fields, and
    -- provides a body.
    Case Term [(DtCnstrName, [Name], Term)]
  deriving stock (Show, Eq, Ord)

instance PP.Pretty Term where
  pretty = prettyTerm lamPrec

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
prettyTerm _ Univ = "Type"
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
prettyTerm _ (AdtTy n []) = PP.pretty n
prettyTerm p (AdtTy n tys) =
  parensIf (p > appPrec) $
    PP.pretty n PP.<+> PP.hsep (map (prettyTerm atomPrec) tys)
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
    SHole Syntax
  | -- | The universe of types.
    SUniv
  | -- | Dependent function type. The body may reference the
    -- bound variable (index 0).
    SPi Name Syntax Syntax
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
    SAdtTy TyCnstrName [Syntax]
  | -- | A data constructor applied to its elaborated
    -- arguments.
    SCnstr DtCnstrName [Syntax]
  | -- | Pattern match on a nominal inductive type. Each
    -- branch pairs a constructor name with an elaborated
    -- body (a lambda over the constructor's fields).
    SCase Syntax [(DtCnstrName, Syntax)]
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
  | -- | The universe of types. @Type : Type@.
    VUniv
  | -- | Dependent function type. The closure computes the
    -- codomain given a value of the domain type.
    VPi Name Value Closure
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
    VAdtTy TyCnstrName [Value]
  | -- | An evaluated data constructor with its argument
    -- values.
    VCnstr DtCnstrName [Value]
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
  | -- | A typed hole. Carries the expected type for
    -- round-trip quoting.
    VHole Syntax
  deriving (Show, Eq, Ord)

-- | A single eliminator in a neutral's spine.
data Frame
  = -- | Term application. Carries the argument's type and
    -- value.
    VApp Value Value
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
    VCase Value [(DtCnstrName, Value)]
  deriving stock (Show, Eq, Ord)

pushFrame :: Neutral -> Frame -> Neutral
pushFrame Neutral {..} frame = Neutral {head = head, spine = Snoc spine frame}

-- | A closure pairing a body with its defining environment.
-- Instantiated by extending the env with a value and
-- evaluating the body.
data Closure = Closure {env :: SnocList Value, body :: Syntax}
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

-- | Surface syntax for a single data constructor declaration. Fields are
-- non-dependent (a plain list of types, no binders), so a field's type
-- cannot refer to an earlier field. See 'elaborateDefinitions' for what
-- introducing dependent fields would require.
data CnstrDecl = CnstrDecl DtCnstrName [Term]
  deriving stock (Show, Eq, Ord)

-- | Core syntax datatype definition. The @Int@ is the type parameter arity.
--
-- For example, the type @data List a = Nil | Cons a (List a)@ becomes
-- (each constructor's type is a Pi-scheme over the parameters):
--
-- > DataTypeSpec "List" 1
-- >   [ Constr "Nil" (SPi "a" SUniv (SAdtTy "List" [SVar 0])),
-- >     Constr "Cons"
-- >       (SPi "a" SUniv (SPi "_" (SVar 0)
-- >         (SPi "_" (SAdtTy "List" [SVar 1]) (SAdtTy "List" [SVar 2]))))
-- >   ]
data DataTypeSpec = DataTypeSpec TyCnstrName Int [DataConstructorSpec]
  deriving stock (Show, Eq, Ord)

-- | Core syntax for a single data constructor. @cnstrType@ holds the
-- constructor's full type: the data type's parameters as leading @SPi@
-- binders over @SUniv@, then the fields, ending in the data type applied
-- to its parameters.
--
-- The @Cons@ constructor of @List a@ becomes the scheme
-- @(a : Type) -> a -> List a -> List a@:
--
-- > Constr "Cons"
-- >   (SPi "a" SUniv (SPi "_" (SVar 0)
-- >     (SPi "_" (SAdtTy "List" [SVar 1]) (SAdtTy "List" [SVar 2]))))
data DataConstructorSpec = Constr
  { cnstrName :: DtCnstrName,
    cnstrType :: Syntax
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
data DataIndex = DataIndex
  { specs :: Map Lvl Def,
    byType :: Map TyCnstrName (Lvl, Int),
    byCnstr :: Map DtCnstrName Lvl
  }
  deriving stock (Show, Eq, Ord)

-- | A single top-level definition: either a datatype ('Data') or a
-- term definition ('Defn') carrying its type and elaborated body.
data Def
  = Data DataTypeSpec
  | Defn Term Syntax
  deriving stock (Show, Eq, Ord)

-- | An index with no definitions, used to bootstrap elaboration of the
-- stock data types.
emptyDataIndex :: DataIndex
emptyDataIndex = DataIndex mempty mempty mempty

-- | Elaborate a batch of surface data declarations into a 'DataIndex' in
-- two phases. Phase 1 registers every type header in @byType@ (with its
-- arity) so that constructor bodies may reference any declared type,
-- including forward and self references. Phase 2 elaborates each
-- constructor, binding the type parameters and building its polymorphic
-- type scheme, and records constructors in @byCnstr@. Both phases reject
-- duplicate type and constructor names.
elaborateDefinitions :: [DataDecl] -> TypecheckM DataIndex
elaborateDefinitions decls = do
  -- Phase 1: Walk the headers
  byType <- foldM insert Map.empty (zip [Lvl 0 ..] decls)

  -- Phase 2: Walk the bodies
  (specs, byCnstr) <-
    local (\env -> env {adtEnv = env.adtEnv {byType}}) $
      foldM elabDecl (Map.empty, Map.empty) (zip [Lvl 0 ..] decls)

  pure $ DataIndex {..}
  where
    insert :: Map TyCnstrName (Lvl, Int) -> (Lvl, DataDecl) -> TypecheckM (Map TyCnstrName (Lvl, Int))
    insert acc (l, DataDecl tyName tyParams _) =
      case Map.lookup tyName acc of
        Just _ -> throwError (DuplicateTypeName tyName)
        Nothing -> pure (Map.insert tyName (l, length tyParams) acc)

    -- Elaborate fields left to right, binding each as an unused cell so the SPi
    -- binders line up; the return is checked under params + all field binders.
    elabFields :: TyCnstrName -> [Name] -> [Term] -> TypecheckM ([Syntax], Syntax)
    elabFields tyName tyParams [] = do
      ret <- runCheck (check (AdtTy tyName (Var <$> tyParams))) VUniv
      pure ([], ret)
    elabFields tyName tyParams (t : rest) = do
      sty <- runCheck (check t) VUniv
      ctx <- ask
      let cell = freshCell ctx "_" (runEvalM (eval sty) (toEvalEnv ctx))
      (restFs, ret) <- local (bindCell cell) (elabFields tyName tyParams rest)
      pure (sty : restFs, ret)

    elabDecl :: (Map Lvl Def, Map DtCnstrName Lvl) -> (Lvl, DataDecl) -> TypecheckM (Map Lvl Def, Map DtCnstrName Lvl)
    elabDecl (specs, byCnstr) (l, DataDecl tyName tyParams cnstrDecls) = do
      dcSpecs <- withTyParams tyParams $ forM cnstrDecls $ \(CnstrDecl dtName argSurfTys) -> do
        -- Each field becomes an 'SPi' binder with an unused ("_") name, so
        -- a field's type cannot reference an earlier field. This keeps the
        -- module parameterized-only: a genuinely dependent constructor like
        -- @MkPoly (Base : Type) (Fiber : Base -> Type)@, where Fiber's type
        -- uses the Base field, is still out of reach. 'elabFields' threads
        -- the context left to right purely so the SPi binders' de Bruijn
        -- levels line up, not to expose fields by name.
        --
        -- The Dependent Pattern Matching module would give CnstrDecl fields
        -- real names (so a later field can reference an earlier one) for
        -- dependent introduction, and make 'constrBranchType' build a
        -- dependent branch type (with 'quote' walking it) for elimination.
        (fieldTys, returnTy) <- elabFields tyName tyParams argSurfTys
        let fieldTele = foldr (\fty acc -> SPi "_" fty acc) returnTy fieldTys
            scheme = foldr (`SPi` SUniv) fieldTele tyParams
        pure $ Constr dtName scheme

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
lookupType :: TyCnstrName -> DataIndex -> Maybe DataTypeSpec
lookupType tyName DataIndex {..} = do
  (lvl, _) <- Map.lookup tyName byType
  Map.lookup lvl specs >>= \case
    Data dtSpec -> pure dtSpec
    Defn _ _ -> Nothing

-- | Look up a data constructor by name, returning its owning type and
-- spec. Returns 'Nothing' if no data type declares it.
lookupCnstr :: DtCnstrName -> DataIndex -> Maybe (TyCnstrName, DataConstructorSpec)
lookupCnstr dtName DataIndex {..} = do
  lvl <- Map.lookup dtName byCnstr
  Map.lookup lvl specs >>= \case
    Data (DataTypeSpec tyName _arity dtSpecs) -> do
      dtSpec <- find (\(Constr dtName' _) -> dtName == dtName') dtSpecs
      pure (tyName, dtSpec)
    Defn _ _ -> Nothing

-- | Look up a constructor by name within a specific data type. Returns
-- 'Nothing' when that type declares no constructor of the name, which is
-- how constructor membership is checked.
lookupCnstrInType :: TyCnstrName -> DtCnstrName -> DataIndex -> Maybe DataConstructorSpec
lookupCnstrInType tyName dtName adtIndex = do
  (DataTypeSpec _ _arity cnstrs) <- lookupType tyName adtIndex
  find (\(Constr dtName' _) -> dtName == dtName') cnstrs

bootstrapEnv :: TypeCheckEnv
bootstrapEnv = TypeCheckEnv Nil [] 0 mempty emptyDataIndex

-- | We predefine a few ADTs here for demonstration purposes. In a complete
-- language these would be defined using 'data' declarations in a module.
stockADTs :: DataIndex
stockADTs =
  either (error . show) id $
    fst $
      runTypecheckM
        ( elaborateDefinitions
            [ DataDecl "Maybe" ["a"] [CnstrDecl "Nothing" [], CnstrDecl "Just" [Var "a"]],
              DataDecl "List" ["a"] [CnstrDecl "Nil" [], CnstrDecl "Cons" [Var "a", AdtTy "List" [Var "a"]]],
              DataDecl "Nat" [] [CnstrDecl "Z" [], CnstrDecl "S" [AdtTy "Nat" []]],
              DataDecl "Wrap" [] [CnstrDecl "MkWrap" [Pi "a" Univ (Var "a" `FuncTy` Var "a")]],
              DataDecl "Fn" [] [CnstrDecl "MkFn" [BoolTy `FuncTy` BoolTy]],
              DataDecl "Dyn" [] [CnstrDecl "MkDyn" [Sigma "a" Univ (Var "a")]]
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
    cellType :: Value,
    cellValue :: Value
  }
  deriving stock (Show, Eq, Ord)

-- | The typechecker/elaboration context. @localValues@ holds
-- values by de Bruijn index, @localValuesNames@ maps names to
-- 'Cell's for resolution, and @localValuesSize@ tracks the
-- current binding depth. Type and term variables share a single
-- index space.
data TypeCheckEnv = TypeCheckEnv
  { localValues :: SnocList Value,
    localValuesNames :: [Cell],
    localValuesSize :: Int,
    -- | Holes encountered during typechecking
    holes :: [Syntax],
    -- | The data type environment (seeded with the stock ADTs).
    adtEnv :: DataIndex
  }
  deriving stock (Show, Eq, Ord)

-- | The evaluator's environment. A snoc list of variable bindings with
-- the current depth, plus the data type environment used when quoting
-- constructors and cases. Used as the top-level eval environment and
-- projected from the typechecker context.
data EvalEnv = EvalEnv
  { -- | Variable bindings, indexed by de Bruijn index.
    evalValues :: SnocList Value,
    -- | Current term binding depth.
    evalValuesLen :: Int,
    -- | The data type environment, for quoting constructors and cases.
    envAdtEnv :: DataIndex
  }
  deriving stock (Show, Eq, Ord)

-- | Project the evaluator environment from the typechecker context. The
-- typechecker carries extra metadata (names, holes, binding depth) that the
-- evaluator does not need.
toEvalEnv :: TypeCheckEnv -> EvalEnv
toEvalEnv env =
  EvalEnv
    { evalValues = env.localValues,
      evalValuesLen = env.localValuesSize,
      envAdtEnv = env.adtEnv
    }

initEnv :: TypeCheckEnv
initEnv = TypeCheckEnv Nil [] 0 mempty stockADTs

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
      holes = holes,
      adtEnv = adtEnv
    }

resolveCell :: TypeCheckEnv -> Name -> Maybe Cell
resolveCell TypeCheckEnv {..} bndr = find ((== bndr) . cellName) localValuesNames

-- | Run an action with a data type's parameters in scope, in declaration
-- order. Each parameter is bound as an ordinary variable of type 'VUniv'
-- (a type), so references in constructor fields elaborate to the expected
-- 'SVar'.
withTyParams :: [Name] -> TypecheckM a -> TypecheckM a
withTyParams tyParams = local $ \typeEnv ->
  foldl' bind typeEnv tyParams
  where
    bind acc name = bindCell (freshCell acc name VUniv) acc

-- | Create a fresh neutral variable at the current depth. Used for lambda-bound
-- variables where we don't know the value.
freshVar :: TypeCheckEnv -> Value -> Value
freshVar TypeCheckEnv {localValuesSize} ty = VNeutral ty $ Neutral (VVar $ Lvl localValuesSize) Nil

-- | Create a fresh cell for a lambda-bound variable. The value is a neutral
-- because we don't know the argument yet.
freshCell :: TypeCheckEnv -> Name -> Value -> Cell
freshCell ctx name ty = Cell name ty (freshVar ctx ty)

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
  Univ -> univFormation
  -- Pi / Function. @A -> B@ is sugar for @Pi _ A B@ (an unused binder).
  Pi nm a b -> piFormation nm (check a) (check b)
  FuncTy a b -> piFormation "_" (check a) (check b)
  -- Sigma / Pair
  Sigma nm a b -> sigmaFormation nm (check a) (check b)
  PairTy a b -> pairTyFormation (check a) (check b)
  Fst tm -> sigmaElimFst (synth tm)
  Snd tm -> sigmaElimSnd (synth tm)
  -- Bool
  BoolTy -> boolFormation
  -- Unit
  UnitTy -> unitFormation
  -- Void
  VoidTy -> voidFormation
  -- Sum
  SumTy a b -> sumFormation (check a) (check b)
  -- Numerics
  NaturalTy -> natFormation
  IntegerTy -> intFormation
  RealTy -> realFormation
  -- Records
  RecordTy fields -> recordFormation (fmap (fmap check) fields)
  Get name tm -> recordElim name (synth tm)
  -- ADTs
  AdtTy nm tys -> adtFormation nm (fmap check tys)
  -- Catch-all
  tm -> Synth $ throwError $ TypeError $ "Cannot synthesize type for " <> show tm

check :: Term -> Check
check = \case
  -- Core
  Lam bndr body -> piIntro bndr (check body)
  Let bndr e body -> letTactic bndr (synth e) (check body)
  Hole -> holeTactic
  -- Sigma / Pair
  Pair tm1 tm2 -> sigmaIntro (check tm1) (check tm2)
  -- Bool
  Tru -> boolIntroTrue
  Fls -> boolIntroFalse
  If tm1 tm2 tm3 -> boolElim (check tm1) (check tm2) (check tm3)
  -- Unit
  Unit -> unitIntro
  -- Void
  Absurd tm -> voidElim (synth tm)
  -- Sum
  InL tm1 -> sumIntroL (check tm1)
  InR tm2 -> sumIntroR (check tm2)
  SumCase scrut (bndr1, t1) (bndr2, t2) -> sumElim (synth scrut) (check (Lam bndr1 t1)) (check (Lam bndr2 t2))
  -- Numerics
  Natural n -> natIntro n
  Integer z -> intIntro z
  Real r -> realIntro r
  -- Records
  Record fields -> recordIntro (fmap (fmap (id &&& check)) fields)
  -- ADTs
  Cnstr nm args -> adtIntro nm (fmap check args)
  Case scrut cases -> adtElim (synth scrut) (fmap (\(x, y, z) -> (x, check (foldr Lam z y))) cases)
  -- Catch-all: switch to synth mode
  tm -> subTactic (synth tm)

-- | Quote a 'Value' back to 'Syntax' from 'TypecheckM'. Projects
-- the eval env and current level from the typechecker context.
quoteValue :: Value -> Value -> TypecheckM Syntax
quoteValue ty val = do
  ctx <- ask
  let l = Lvl ctx.localValuesSize
  pure $ runEvalM (quote l ty val) (toEvalEnv ctx)

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
      let quoted = flip runEvalM (toEvalEnv ctx) $ quote (Lvl ctx.localValuesSize) cellType cellValue
      pure (cellType, quoted)
    Nothing -> throwError $ UnknownVariable bndr

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
--  Γ ⊢ A ⇐ Type    Γ ⊢ e ⇐ A
--  ─────────────────────────── Anno⇒
--       Γ ⊢ (e : A) ⇒ A
annoTactic :: Term -> Check -> Synth
annoTactic ty (Check bodyTac) = Synth $ do
  sty <- runCheck (check ty) VUniv
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
  VPi _ a clo -> do
    var <- asks $ \ctx -> freshCell ctx bndr a
    fiber <- local (bindCell var) $ do
      ctx <- asks toEvalEnv
      let b = runEvalM (appClosure clo var.cellValue) ctx
      bodyTac b
    pure $ SLam bndr fiber
  ty -> throwError $ TypeError $ "Tried to introduce a lambda at a non-function type: " <> show ty

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
      (VPi _ a clo, f) -> do
        arg <- argTac a
        ctx <- asks toEvalEnv
        let vArg = runEvalM (eval arg) ctx
            b = runEvalM (appClosure clo vArg) ctx
        pure (b, SAp f arg)
      (ty, _) -> throwError $ TypeError $ "Expected a function type but got " <> show ty

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
  ty <- quoteValue VUniv ty
  tell (Holes [ty])
  pure (SHole ty)

-- | Universe Formation
--
-- @Type : Type@. Inconsistent but simple.
--
-- ──────────────── Univ⇒
-- Γ ⊢ Type ⇒ Type
univFormation :: Synth
univFormation = Synth $ pure (VUniv, SUniv)

-- | Pi Formation
--
-- Synthesizes @Type@ for a dependent function type. The domain is checked
-- against @Type@, then a fresh variable of the domain type is introduced so the
-- codomain can reference it. The codomain is checked against @Type@ in the
-- extended context. Elaborates to @SPi nm sa sb@.
--
--  Γ ⊢ A ⇐ Type    Γ, x : A ⊢ B ⇐ Type
--  ─────────────────────────────────── Pi⇒
--         Γ ⊢ (x : A) → B ⇒ Type
piFormation :: Name -> Check -> Check -> Synth
piFormation nm (Check domTac) (Check codTac) = Synth $ do
  sa <- domTac VUniv
  ctx <- ask
  let va = runEvalM (eval sa) (toEvalEnv ctx)
      var = freshCell ctx nm va
  sb <- local (bindCell var) $ codTac VUniv
  pure (VUniv, SPi nm sa sb)

-- | Sigma Formation
--
-- Synthesizes @Type@ for a dependent pair type. The first component's type is
-- checked against @Type@, then a fresh variable of that type is introduced so
-- the second component's type can reference it. The second component's type is
-- checked against @Type@ in the extended context. Elaborates to @SSigma nm sa
-- sb@.
--
--  Γ ⊢ A ⇐ Type    Γ, x : A ⊢ B ⇐ Type
--  ─────────────────────────────────── Sigma⇒
--         Γ ⊢ (x : A) × B ⇒ Type
sigmaFormation :: Name -> Check -> Check -> Synth
sigmaFormation nm (Check domTac) (Check codTac) = Synth $ do
  sa <- domTac VUniv
  ctx <- ask
  let va = runEvalM (eval sa) (toEvalEnv ctx)
      var = freshCell ctx nm va
  sb <- local (bindCell var) $ codTac VUniv
  pure (VUniv, SSigma nm sa sb)

-- | Pair Type Formation
--
-- Non-dependent pair type. Both components are checked against
-- @Type@. Elaborates to @SPairTy@.
--
-- Γ ⊢ A ⇐ Type    Γ ⊢ B ⇐ Type
-- ──────────────────────────── Pair⇒
--      Γ ⊢ A × B ⇒ Type
pairTyFormation :: Check -> Check -> Synth
pairTyFormation (Check fstTac) (Check sndTac) = Synth $ do
  sa <- fstTac VUniv
  sb <- sndTac VUniv
  pure (VUniv, SPairTy sa sb)

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
-- ──────────────── Bool⇒
-- Γ ⊢ Bool ⇒ Type
boolFormation :: Synth
boolFormation = Synth $ pure (VUniv, SBoolTy)

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
  tm1 <- checkT1 VBoolTy
  tm2 <- checkT2 ty
  tm3 <- checkT3 ty
  ty <- quoteValue VUniv ty
  pure (SIf tm1 ty tm2 tm3)

-- | Unit Formation
--
-- ──────────────── Unit⇒
-- Γ ⊢ Unit ⇒ Type
unitFormation :: Synth
unitFormation = Synth $ pure (VUniv, SUnitTy)

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
-- ──────────────── Void⇒
-- Γ ⊢ Void ⇒ Type
voidFormation :: Synth
voidFormation = Synth $ pure (VUniv, SVoidTy)

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
      ty <- quoteValue VUniv ty
      pure $ SAbsurd ty scrut
    _ -> throwError $ TypeError $ "Expected a Void but got: " <> show scrutTy

-- | Sum Formation
--
-- Both components are checked against @Type@. Elaborates to
-- @SSumTy@.
--
-- Γ ⊢ A ⇐ Type    Γ ⊢ B ⇐ Type
-- ──────────────────────────── Sum⇒
--      Γ ⊢ A + B ⇒ Type
sumFormation :: Check -> Check -> Synth
sumFormation (Check lTac) (Check rTac) = Synth $ do
  sa <- lTac VUniv
  sb <- rTac VUniv
  pure (VUniv, SSumTy sa sb)

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
-- Synthesize the scrutinee's sum type, then check each branch as a
-- function from the injection's payload type to the motive. The
-- branches are elaborated as lambdas that bind the payload.
--
--  Γ ⊢ e ⇒ A + B    Γ ⊢ f ⇐ A → C    Γ ⊢ g ⇐ B → C
--  ─────────────────────────────────────────────── SumCase⇐
--                Γ ⊢ SumCase e f g ⇐ C
sumElim :: Synth -> Check -> Check -> Check
sumElim (Synth synth) (Check checkT1) (Check checkT2) = Check $ \motiv -> do
  (scrutTy, scrut) <- synth
  case scrutTy of
    VSumTy a b -> do
      ctx <- ask
      let fTy = runEvalM (vArrow a motiv) (toEvalEnv ctx)
          gTy = runEvalM (vArrow b motiv) (toEvalEnv ctx)
      f <- checkT1 fTy
      g <- checkT2 gTy
      motiv <- quoteValue VUniv motiv
      pure $ SSumCase scrut motiv f g
    _ -> throwError $ TypeError $ "Expected a Sum type but got: " <> show scrutTy

-- | Natural Type Formation
--
-- ──────────────── Nat⇒
-- Γ ⊢ Nat ⇒ Type
natFormation :: Synth
natFormation = Synth $ pure (VUniv, SNaturalTy)

-- | Integer Type Formation
--
-- ──────────────── Int⇒
-- Γ ⊢ Int ⇒ Type
intFormation :: Synth
intFormation = Synth $ pure (VUniv, SIntegerTy)

-- | Real Type Formation
--
-- ──────────────── Real⇒
-- Γ ⊢ Real ⇒ Type
realFormation :: Synth
realFormation = Synth $ pure (VUniv, SRealTy)

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

-- | Record Type Formation
--
-- Each field type is checked against @Type@. Elaborates to
-- @SRecordTy@.
--
--        Γ ⊢ Tᵢ ⇐ Type (i ∈ 1..n)
-- ──────────────────────────────────── Record⇒
-- Γ ⊢ { lᵢ : Tᵢ (i ∈ 1..n) } ⇒ Type
recordFormation :: [(Name, Check)] -> Synth
recordFormation fields = Synth $ do
  fields' <- forM fields $ \(nm, Check tac) -> do
    sty <- tac VUniv
    pure (nm, sty)
  pure (VUniv, SRecordTy fields')

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

-- | ADT Type Formation
--
-- Each type argument is checked against @Type@. Elaborates to
-- @SAdtTy@.
--
--     Γ ⊢ Tᵢ ⇐ Type (i ∈ 1..n)
-- ──────────────────────────────── ADT⇒
--      Γ ⊢ T T₁...Tₙ ⇒ Type
adtFormation :: TyCnstrName -> [Check] -> Synth
adtFormation nm tys = Synth $ do
  tys' <- forM tys $ \(Check tac) -> tac VUniv
  pure (VUniv, SAdtTy nm tys')

-- | ADT Introduction
--
-- Checked against a type whose return position is an ADT type. The expected
-- type is decomposed by peeling off function arrows until the return type @T ā@
-- is found. The type arguments @ā@ specialize the constructor's scheme
-- before its fields are checked.
--
-- Supports partial application via eta expansion. When fewer than @n@ term
-- arguments are provided, the constructor is wrapped in lambdas for all @n@
-- fields and the provided arguments are applied, leaving a function that
-- accepts the remaining fields.
--
-- For example, given @data Maybe a = Nothing | Just a@:
--
-- @(Just True : Maybe Bool)@: the expected type is @Maybe Bool@, so @Just@'s
-- scheme @(a : Type) -> a -> Maybe a@ is instantiated at @Bool@ to give
-- @Bool -> Maybe Bool@, and @True@ is checked against @Bool@.
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
  ctx <- ask
  let lvl = Lvl ctx.localValuesSize
      (returnTy, _) = runEvalM (decomposeFunction lvl expectedTy) (toEvalEnv ctx)
  case returnTy of
    VAdtTy tyName tys -> do
      adtMap <- asks adtEnv
      case lookupCnstrInType tyName nm adtMap of
        Just dtSpec -> do
          let constrTy = runEvalM (instantiateScheme dtSpec.cnstrType tys) (toEvalEnv ctx)
              (_returnTy, paramTys) = runEvalM (decomposeFunction lvl constrTy) (toEvalEnv ctx)
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

instantiateScheme :: Syntax -> [Value] -> EvalM Value
instantiateScheme scheme vtys = do
  vScheme <- eval scheme
  foldM apply vScheme vtys
  where
    apply :: Value -> Value -> EvalM Value
    apply (VPi _ _ body) ty = appClosure body ty
    apply _ _ = error "impossible case: instantiateScheme applied a non-forall"

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
-- types come from instantiating the constructor's scheme at the
-- scrutinee's type arguments, so for a @List Bool@ scrutinee the
-- parameter @a@ becomes @Bool@. This is a non-recursive case, not a fold:
-- a recursive field (the second field of Cons) stays @List Bool@, so the
-- branch receives the substructure itself rather than an already
-- eliminated result. The goal type A is the type of each branch body.
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
    VAdtTy tyName tys -> do
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

-- | Decompose a function into its return type and a list of its args.
decomposeFunction :: Lvl -> Value -> EvalM (Value, [Value])
decomposeFunction l (VPi _ dom cod) = do
  -- binder unused here, so the fresh var is harmless
  rest <- appClosure cod (VNeutral dom (Neutral (VVar l) Nil))
  (ret, doms) <- decomposeFunction (incLevel l) rest
  pure (ret, dom : doms)
decomposeFunction _ ty = pure (ty, [])

-- | The type a single case branch is checked against: each constructor
-- field becomes a function argument, ending in the goal type.
--
-- The field types come from instantiating the constructor's polymorphic scheme
-- at the scrutinee's type arguments. Recursive fields keep their data type
-- (this is case analysis, not a fold).
constrBranchType :: EvalEnv -> Value -> [Value] -> DataConstructorSpec -> (DtCnstrName, Value)
constrBranchType evalEnv motive tys (Constr nm scheme) =
  let build = do
        instTy <- instantiateScheme scheme tys
        (_ret, fields) <- decomposeFunction (Lvl evalEnv.evalValuesLen) instTy
        foldrM vArrow motive fields
   in (nm, runEvalM build evalEnv)

-- | The branch types for every constructor of a data type, used to check
-- each arm of a case expression.
caseBranchTypes :: EvalEnv -> Value -> [Value] -> DataTypeSpec -> [(DtCnstrName, Value)]
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
isSubtypeOf :: Lvl -> Value -> Value -> EvalM Bool
isSubtypeOf l (VPi _ a1 clo1) (VPi _ a2 clo2) = do
  domOk <- isSubtypeOf l a2 a1
  let x = VNeutral a2 $ Neutral (VVar l) Nil
  cod1 <- appClosure clo1 x
  cod2 <- appClosure clo2 x
  codOk <- isSubtypeOf (incLevel l) cod1 cod2
  pure (domOk && codOk)
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
equateNeutral :: Lvl -> Neutral -> Neutral -> EvalM Bool
equateNeutral l (Neutral h1 s1) (Neutral h2 s2) =
  if h1 == h2
    then equateSpine l s1 s2
    else pure False

-- | Walk two spines pairwise, checking each frame for equality.
-- Mismatched lengths return 'False'.
equateSpine :: Lvl -> SnocList Frame -> SnocList Frame -> EvalM Bool
equateSpine _ Nil Nil = pure True
equateSpine l (Snoc s1 f1) (Snoc s2 f2) = do
  restOk <- equateSpine l s1 s2
  frameOk <- equateFrame l f1 f2
  pure (restOk && frameOk)
equateSpine _ _ _ = pure False

-- | Check two eliminator frames for definitional equality.
-- Uses 'equateValue' (not subtyping) for values in the spine,
-- since we can't determine the variance of a stuck head.
equateFrame :: Lvl -> Frame -> Frame -> EvalM Bool
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
equateValue :: Lvl -> Value -> Value -> EvalM Bool
equateValue l (VNeutral _ n1) (VNeutral _ n2) =
  equateNeutral l n1 n2
equateValue l (VLam _ clo1) (VLam _ clo2) = do
  let x = VNeutral VUnit $ Neutral (VVar l) Nil
  b1 <- appClosure clo1 x
  b2 <- appClosure clo2 x
  equateValue (incLevel l) b1 b2
equateValue _ VUniv VUniv = pure True
equateValue l (VPi _ a1 clo1) (VPi _ a2 clo2) = do
  aOk <- equateValue l a1 a2
  let x = VNeutral a1 $ Neutral (VVar l) Nil
  b1 <- appClosure clo1 x
  b2 <- appClosure clo2 x
  bOk <- equateValue (incLevel l) b1 b2
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
recordSubtype :: Lvl -> Value -> Value -> EvalM Bool
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
    env <- asks evalValues
    pure $ fromMaybe (error "internal error") $ nth env ix
  SLam bndr body -> do
    env <- asks evalValues
    pure $ VLam bndr (Closure env body)
  SAp tm1 tm2 -> do
    fun <- eval tm1
    arg <- eval tm2
    doApply fun arg
  SHole sty -> do
    vty <- eval sty
    pure $ VNeutral vty (Neutral (VHole sty) Nil)
  -- Universe
  SUniv -> pure VUniv
  -- Pi / Function
  SPi nm a b -> do
    env <- asks evalValues
    a <- eval a
    pure $ VPi nm a $ Closure env b
  -- Sigma / Pair
  SSigma nm a b -> do
    env <- asks evalValues
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
  SInL tm -> eval tm <&> VInL
  SInR tm -> eval tm <&> VInR
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
doApply (VNeutral (VPi _ a clo) neu) arg = do
  fiber <- appClosure clo arg
  pure $ VNeutral fiber (pushFrame neu (VApp a arg))
doApply _ _ = error "impossible case in doApply"

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
  tyF <- vArrow a motive
  tyG <- vArrow b motive
  pure $ VNeutral motive (pushFrame neu (VSumCase tyF tyG motive f g))
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

-- | Instantiate a closure by extending the env with a value and
-- evaluating the body.
appClosure :: Closure -> Value -> EvalM Value
appClosure (Closure env body) v =
  local (\e -> e {evalValues = Snoc env v}) $ eval body

--------------------------------------------------------------------------------
-- Quoting
--
-- Quoting reads back a 'Value' into 'Syntax' (normal form). It
-- is type-directed: the 'Value' type argument tells us how to
-- handle each value.
--
-- Key cases dispatch on the type:
--
-- 1. At 'VPi': eta-expand. Generate a fresh
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

quote :: Lvl -> Value -> Value -> EvalM Syntax
quote l = \cases
  -- Neutral
  _ (VNeutral _ neu) -> quoteNeutral l neu
  -- Pi / Function: eta-expand
  (VPi _nm a clo) (VLam bndr body) -> do
    b <- bindVar a l $ \v l' -> do
      fiber <- appClosure clo v
      body' <- appClosure body v
      quote l' fiber body'
    pure $ SLam bndr b
  (VPi _nm a clo) f -> do
    b <- bindVar a l $ \v l' -> do
      fiber <- appClosure clo v
      doApply f v >>= quote l' fiber
    pure $ SLam "_" b
  -- Sigma / Pair: quote components
  (VSigma _bndr a clo) (VPair tm1 tm2) -> do
    tm1' <- quote l a tm1
    fiber <- appClosure clo tm1
    tm2' <- quote l fiber tm2
    pure $ SPair tm1' tm2'
  (VPairTy ty1 ty2) (VPair tm1 tm2) -> do
    tm1' <- quote l ty1 tm1
    tm2' <- quote l ty2 tm2
    pure $ SPair tm1' tm2'
  -- Bool
  _ VTru -> pure STru
  _ VFls -> pure SFls
  -- Unit
  _ VUnit -> pure SUnit
  -- Sum
  (VSumTy a _b) (VInL tm) -> SInL <$> quote l a tm
  (VSumTy _a b) (VInR tm) -> SInR <$> quote l b tm
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
              Just fty -> (nm,) <$> quote l fty val
              Nothing -> error "impossible: field not in type."
        )
  -- ADTs
  (VAdtTy tyName vtys) (VCnstr nm args) -> do
    adtEnv <- asks envAdtEnv
    case lookupCnstrInType tyName nm adtEnv of
      Just (Constr _ scheme) -> do
        instTy <- instantiateScheme scheme vtys
        (_ret, argTys) <- decomposeFunction l instTy
        SCnstr nm <$> zipWithM (quote l) argTys args
      Nothing ->
        error "impossible case in quote: constructor not found in its data type"
  -- Quoting types as values (at VUniv)
  _ VUniv -> pure SUniv
  _ (VPi nm a clo) -> do
    a' <- quote l VUniv a
    b' <- bindVar a l $ \v l' -> do
      fiber <- appClosure clo v
      quote l' VUniv fiber
    pure $ SPi nm a' b'
  _ (VSigma bndr a clo) -> do
    a' <- quote l VUniv a
    b <- bindVar a l $ \v l' -> do
      fiber <- appClosure clo v
      quote l' VUniv fiber
    pure $ SSigma bndr a' b
  _ (VPairTy t1 t2) -> do
    t1 <- quote l VUniv t1
    t2 <- quote l VUniv t2
    pure $ SPairTy t1 t2
  _ VBoolTy -> pure SBoolTy
  _ VUnitTy -> pure SUnitTy
  _ VVoidTy -> pure SVoidTy
  _ (VSumTy t1 t2) -> do
    t1 <- quote l VUniv t1
    t2 <- quote l VUniv t2
    pure $ SSumTy t1 t2
  _ VNaturalTy -> pure SNaturalTy
  _ VIntegerTy -> pure SIntegerTy
  _ VRealTy -> pure SRealTy
  _ (VRecordTy fields) -> do
    fields <- forM fields (traverse $ quote l VUniv)
    pure $ SRecordTy fields
  _ (VAdtTy nm tys) -> do
    tys <- traverse (quote l VUniv) tys
    pure $ SAdtTy nm tys
  -- Catch-all
  ty tm -> error $ "impossible case in quote:\n" <> show ty <> "\n" <> show tm

-- | Build the non-dependent function type @dom -> cod@ as a 'VPi' with an
-- unused binder. Since 'cod' is already a value, we quote it back one level
-- deeper (under the binder) so the closure reproduces it when applied.
vArrow :: Value -> Value -> EvalM Value
vArrow dom cod = do
  env <- ask
  codS <- quote (incLevel (Lvl env.evalValuesLen)) VUniv cod -- quote at depth+1
  pure $ VPi "_" dom (Closure env.evalValues codS)

quoteLevel :: Lvl -> Lvl -> Ix
quoteLevel (Lvl l) (Lvl x) = Ix (l - (x + 1))

quoteNeutral :: Lvl -> Neutral -> EvalM Syntax
quoteNeutral l Neutral {..} = foldM (quoteFrame l) (quoteHead l head) spine

quoteHead :: Lvl -> Head -> Syntax
quoteHead l (VVar lvl) = SVar (quoteLevel l lvl)
quoteHead _ (VHole ty) = SHole ty

quoteFrame :: Lvl -> Syntax -> Frame -> EvalM Syntax
quoteFrame l tm = \case
  -- Pi / Function
  VApp ty arg -> SAp tm <$> quote l ty arg
  -- Sigma / Pair
  VFst -> pure $ SFst tm
  VSnd -> pure $ SSnd tm
  -- Bool
  VIf ty t1 t2 -> do
    sty <- quote l VUniv ty
    liftA2 (SIf tm sty) (quote l ty t1) (quote l ty t2)
  -- Void
  VAbsurd vty -> do
    sty <- quote l VUniv vty
    pure $ SAbsurd sty tm
  -- Sum
  VSumCase tyF tyG mot f g -> do
    f' <- quote l tyF f
    g' <- quote l tyG g
    mot <- quote l VUniv mot
    pure $ SSumCase tm mot f' g'
  -- Records
  VGet name -> pure $ SGet name tm
  -- ADTs
  VCase mot cases -> SCase tm <$> traverse (traverse (quote l mot)) cases

-- | Introduce a fresh term variable at the given level. Creates a neutral value
-- at the given type and passes it (along with the incremented level) to the
-- continuation. Used by quoting to eta-expand at function types.
bindVar :: Value -> Lvl -> (Value -> Lvl -> a) -> a
bindVar ty lvl f =
  let v = VNeutral ty $ Neutral (VVar lvl) Nil
   in f v $ incLevel lvl

--------------------------------------------------------------------------------
-- Main

run :: Term -> Either (Error, Holes) (RunResult Syntax Syntax Syntax Value, Holes)
run term =
  case runTypecheckM (runSynth $ synth term) initEnv of
    (Left err, holes) -> Left (err, holes)
    (Right (type', syntax), holes) -> do
      let evalEnv = toEvalEnv initEnv
          value = runEvalM (eval syntax) evalEnv
          result = runEvalM (quote initLevel type' value) evalEnv
          quotedType = runEvalM (quote initLevel VUniv type') evalEnv
      pure (RunResult syntax quotedType result value, holes)

-- | This module's mapping of the shared core vocabulary onto its own
-- constructors. Types are collapsed into terms here, so the vocab's surface
-- type is 'Term' and the type formers are ordinary 'Term' constructors.
foundationVocab :: CoreVocab Term Term
foundationVocab =
  CoreVocab
    { var = Var . Name,
      lam = Lam . Name,
      ap = Ap,
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
  putStrLn "=== MLTT ==="
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

    -- Dependent identity
    section "Dependent Functions"
    test
      "dependent id applied to Bool"
      ( Ap
          ( Ap
              ( Anno
                  (Pi "a" Univ (FuncTy (Var "a") (Var "a")))
                  (Lam "a" (Lam "x" (Var "x")))
              )
              BoolTy
          )
          (Anno BoolTy Tru)
      )
      (Anno BoolTy Tru)
    test
      "dependent id applied to Unit"
      ( Ap
          ( Ap
              ( Anno
                  (Pi "a" Univ (FuncTy (Var "a") (Var "a")))
                  (Lam "a" (Lam "x" (Var "x")))
              )
              UnitTy
          )
          Unit
      )
      (Anno UnitTy Unit)
    smoke
      "dependent id unapplied"
      ( Anno
          (Pi "a" Univ (FuncTy (Var "a") (Var "a")))
          (Lam "a" (Lam "x" (Var "x")))
      )

    -- Dependent const
    section "Dependent Const"
    test
      "dependent const applied to Bool and Unit"
      ( Ap
          ( Ap
              ( Ap
                  ( Ap
                      ( Anno
                          (Pi "a" Univ (Pi "b" Univ (FuncTy (Var "a") (FuncTy (Var "b") (Var "a")))))
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
      (Anno BoolTy Tru)

    -- Dependent apply
    section "Dependent Apply"
    test
      "dependent apply with not"
      ( Ap
          ( Ap
              ( Ap
                  ( Ap
                      ( Anno
                          (Pi "a" Univ (Pi "b" Univ (FuncTy (FuncTy (Var "a") (Var "b")) (FuncTy (Var "a") (Var "b")))))
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
      (Anno BoolTy Fls)

    -- Basic types
    section "Basic Types"
    test
      "Bool is a type"
      (Anno Univ BoolTy)
      (Anno Univ BoolTy)
    test
      "Unit is a type"
      (Anno Univ UnitTy)
      (Anno Univ UnitTy)
    smoke
      "function type is a type"
      (Anno Univ (FuncTy BoolTy BoolTy))
    smoke
      "Pi type is a type"
      (Anno Univ (Pi "a" Univ (FuncTy (Var "a") (Var "a"))))

    -- ADTs
    section "ADTs - Maybe"
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

    section "ADTs - List"
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

    section "ADTs - Partial Application"
    smoke
      "partially applied Just"
      (Anno (FuncTy BoolTy (AdtTy "Maybe" [BoolTy])) (Cnstr "Just" []))
    smoke
      "fully unapplied Cons"
      ( Anno
          (FuncTy BoolTy (FuncTy (AdtTy "List" [BoolTy]) (AdtTy "List" [BoolTy])))
          (Cnstr "Cons" [])
      )

    section "ADTs - Errors"
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
      "MkWrap (\\a. \\x. x) at Wrap"
      (Anno (AdtTy "Wrap" []) (Cnstr "MkWrap" [Lam "a" (Lam "x" (Var "x"))]))

    -- Type : Type
    section "Type in Type"
    test
      "Type is a type"
      (Anno Univ Univ)
      (Anno Univ Univ)
    smoke
      "Sigma type is a type"
      (Anno Univ (Sigma "a" Univ (FuncTy (Var "a") (Var "a"))))

    -- Dependent pairs
    section "Dependent Pairs"
    test
      "non-dependent pair"
      ( Anno
          (PairTy BoolTy UnitTy)
          (Pair Tru Unit)
      )
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
      (Anno BoolTy Tru)
    test
      "snd of non-dependent pair"
      ( Snd
          ( Anno
              (PairTy BoolTy UnitTy)
              (Pair Tru Unit)
          )
      )
      (Anno UnitTy Unit)

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
      (Anno NaturalTy (Natural 7))
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
      (Anno UnitTy Unit)

    -- Records
    section "Records"
    test
      "record literal"
      ( Anno
          (RecordTy [("x", BoolTy), ("y", UnitTy)])
          (Record [("x", Tru), ("y", Unit)])
      )
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
      (Anno BoolTy Tru)

    -- Subtyping
    section "Subtyping"
    test
      "Nat as Int"
      (Anno IntegerTy (Natural 5))
      (Anno IntegerTy (Natural 5))
    test
      "Nat as Real"
      (Anno RealTy (Natural 5))
      (Anno RealTy (Natural 5))
    test
      "Int as Real"
      (Anno RealTy (Integer 42))
      (Anno RealTy (Integer 42))

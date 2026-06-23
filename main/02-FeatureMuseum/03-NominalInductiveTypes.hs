{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- | Nominal Inductive Types.
--
-- Adds user-defined algebraic data types with named constructors. Each
-- 'DataTypeSpec' declares a type name and a list of 'DataConstructorSpec's with
-- typed fields (including recursive references via 'Rec'). Constructors are
-- introduced by 'Cnstr' and eliminated by 'Case', which pattern-matches on the
-- constructor name and binds the fields. Constructors support partial
-- application via eta-expansion around the constructor's function type.
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
import Data.Either (fromRight)
import Data.Foldable (find)
import Data.Map (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Scientific (Scientific)
import Data.String
import Data.These
import PrettyTerm (Prec, appPrec, arrowPrec, arrowSym, atomPrec, lamPrec, lambdaSym, parensIf, sumPrec)
import PrettyTerm qualified as PP
import TestHarness (RunResult (..), runTest, runTestErr, section)
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
    Ap Term Term
  | -- | Let binding. @let x = t1 in t2@
    Let Name Term Term
  | -- | A term with a type annotation that we ignore during evaluation. @(t : A)@
    Anno Type Term
  | -- | A missing subterm. Can only appear in check position (where the
    -- expected type is known). In synth position it's an error.
    Hole
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
    prettyTerm (lamPrec + 1) e PP.<+> ":" PP.<+> prettyType lamPrec ty
prettyTerm _ Hole = "_"
prettyTerm _ (Pair a b) =
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
  = -- | Function type. @A -> B@.
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
    AdtTy TyCnstrName
  deriving stock (Show, Eq, Ord)

prettyType :: Prec -> Type -> PP.Doc ann
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
prettyType _ (AdtTy n) = PP.pretty n

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
    SHole Type
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
    SIf Syntax Type Syntax Syntax
  | -- | The unit value.
    SUnit
  | -- | Elimination of the empty type. @absurd t@.
    SAbsurd Type Syntax
  | -- | Left injection into a sum type. @inl x@.
    SInL Syntax
  | -- | Right injection into a sum type. @inr x@.
    SInR Syntax
  | -- | Case analysis on a sum type. @case scrut of inl x -> l; inr y -> r@.
    SSumCase Syntax Type Syntax Syntax
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
  | -- | Pattern match on a nominal inductive type. The 'Type' is the
    -- result type. Each remaining pair is a constructor name and an
    -- elaborated body, a lambda over the constructor's fields. The result
    -- type is retained so a case on a neutral scrutinee can be read back,
    -- quoting each branch at its branch type.
    SCase Syntax Type [(DtCnstrName, Syntax)]
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
    VNeutral Type Neutral
  | -- | A closure: the lambda body paired with its defining environment.
    -- Application triggers beta reduction by extending this environment.
    VLam Name Closure
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

data Head
  = VVar Lvl
  | VHole Type
  deriving (Show, Eq, Ord)

-- | A single eliminator in a neutral's spine.
data Frame
  = VApp Type Value
  | VFst
  | VSnd
  | -- | A stuck if-then-else: the condition is neutral, so we can't choose a
    -- branch. Carries the motive type and both branch values.
    VIf Type Value Value
  | -- | A stuck absurd: the scrutinee is neutral at 'VoidTy'.
    VAbsurd Type
  | -- | A stuck case: the scrutinee is neutral.
    VSumCase Type Type Type Value Value
  | -- | A stuck record projection.
    VGet Name
  | -- | A stuck nominal case: the scrutinee is neutral. The first 'Type'
    -- is the scrutinee's data type and the second is the result type. Both
    -- are needed to read each branch back at its branch type.
    VCase Type Type [(DtCnstrName, Value)]
  deriving stock (Show, Eq, Ord)

pushFrame :: Neutral -> Frame -> Neutral
pushFrame Neutral {..} frame = Neutral {head = head, spine = Snoc spine frame}

-- | A closure pairs a function body with the environment it was defined in.
-- Instantiation extends the captured environment with the argument rather than
-- substituting. Closures also appear inside neutrals (as arguments in 'VApp'
-- frames).
data Closure = Closure {env :: EvalEnv, body :: Syntax}
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
data DataDecl = DataDecl TyCnstrName [CnstrDecl]
  deriving stock (Show, Eq, Ord)

-- | Surface syntax for a single data constructor declaration.
data CnstrDecl = CnstrDecl DtCnstrName [TypeRef]
  deriving stock (Show, Eq, Ord)

-- | Surface syntax for the types that may appear in constructor fields. A
-- 'TyRef' names another declared data type; the remaining forms mirror
-- the built-in type formers.
data TypeRef
  = TyRef TyCnstrName
  | TyRefFunc TypeRef TypeRef
  | TyRefPair TypeRef TypeRef
  | TyRefSum TypeRef TypeRef
  | TyRefBool
  | TyRefUnit
  | TyRefVoid
  | TyRefNatural
  | TyRefInteger
  | TyRefReal
  | TyRefRecord [(Name, TypeRef)]
  deriving stock (Show, Eq, Ord)

-- | Core syntax datatype definition.
--
-- For example, the type @ListBool = Nil | Cons Bool ListBool@ becomes:
--
-- > DataTypeSpec "ListBool"
-- >   [ Constr "Nil" [] (AdtTy "ListBool"),
-- >     Constr
-- >       "Cons"
-- >       [BoolTy, AdtTy "ListBool"]
-- >       (FuncTy BoolTy (FuncTy (AdtTy "ListBool") (AdtTy "ListBool")))
-- >   ]
data DataTypeSpec = DataTypeSpec TyCnstrName [DataConstructorSpec]
  deriving stock (Show, Eq, Ord)

-- | Core syntax for a single data constructor.
--
-- The @Cons@ constructor of @ListBool@, taking a @Bool@ and a recursive
-- @ListBool@, becomes:
--
-- > Constr
-- >   "Cons"
-- >   [BoolTy, AdtTy "ListBool"]
-- >   (FuncTy BoolTy (FuncTy (AdtTy "ListBool") (AdtTy "ListBool")))
--
-- NOTE: The @cnstrType@ field caches the full constructor function type built
-- from the argument types.
data DataConstructorSpec = Constr
  { cnstrName :: DtCnstrName,
    cnstrArgs :: [Type],
    cnstrType :: Type
  }
  deriving stock (Show, Eq, Ord)

-- | The collection of top-level definitions, with name-based indices
-- for resolving references during elaboration.
--
-- @specs@ is the canonical store, keyed by 'Lvl'. @byType@ and @byCnstr@
-- map surface names to levels and exist only so the elaborator can
-- resolve a written name to its definition. @byType@ maps each type to
-- its level. @byCnstr@ maps each constructor to the level of its owning
-- type.
data AdtIndex = AdtIndex
  { specs :: Map Lvl Def,
    byType :: Map TyCnstrName Lvl,
    byCnstr :: Map DtCnstrName Lvl
  }
  deriving stock (Show, Eq, Ord)

-- | A single top-level definition: either a datatype ('Data') or a
-- term definition ('Defn') carrying its type and elaborated body.
data Def
  = Data DataTypeSpec
  | Defn Type Syntax
  deriving stock (Show, Eq, Ord)

-- | Errors that can arise while elaborating data declarations.
data AdtError = DuplicateTypeName TyCnstrName | DuplicateConstructorName DtCnstrName | UnknownTypeReference TyCnstrName
  deriving stock (Show, Eq, Ord)

-- | Elaborate a batch of surface data declarations into an 'AdtIndex' in
-- two phases. Phase 1 registers every type header in @byType@ so that
-- constructor bodies may reference any declared type, including forward
-- and self references. Phase 2 resolves each constructor's field types
-- and caches its function type, recording constructors in @byCnstr@. Both
-- phases reject duplicate type and constructor names.
elaborateDefinitions :: [DataDecl] -> Either AdtError AdtIndex
elaborateDefinitions decls = do
  -- Phase 1: Walk the headers
  byType <- foldM insert Map.empty (zip [Lvl 0 ..] decls)

  -- Phase 2: Walk the bodies
  (specs, byCnstr) <- foldM (elabDecl byType) (Map.empty, Map.empty) (zip [Lvl 0 ..] decls)

  pure AdtIndex {..}
  where
    insert acc (l, DataDecl tyName _) =
      case Map.lookup tyName acc of
        Just _ -> Left (DuplicateTypeName tyName)
        Nothing -> Right (Map.insert tyName l acc)
    elabDecl :: Map TyCnstrName Lvl -> (Map Lvl Def, Map DtCnstrName Lvl) -> (Lvl, DataDecl) -> Either AdtError (Map Lvl Def, Map DtCnstrName Lvl)
    elabDecl byType (specs, byCnstr) (l, DataDecl tyName cnstrDecls) = do
      dcSpecs <- forM cnstrDecls $ \(CnstrDecl dtName typeRefs) -> do
        args <- traverse (resolveTypeRef byType) typeRefs
        let cnstrType = foldr FuncTy (AdtTy tyName) args
        pure $ Constr dtName args cnstrType
      let def = Data $ DataTypeSpec tyName dcSpecs
          specs' = Map.insert l def specs
      byCnstr' <-
        foldM
          ( \acc spec ->
              Map.alterF (\case Just _ -> Left $ DuplicateConstructorName spec.cnstrName; Nothing -> Right $ Just l) spec.cnstrName acc
          )
          byCnstr
          dcSpecs
      pure (specs', byCnstr')

-- | Resolve a surface 'TypeRef' to a core 'Type', checking that every
-- referenced data type is declared. Fails with 'UnknownTypeReference' for
-- an unbound type name.
resolveTypeRef :: Map TyCnstrName Lvl -> TypeRef -> Either AdtError Type
resolveTypeRef byType = go
  where
    go = \case
      TyRef tyName
        | Map.member tyName byType -> pure (AdtTy tyName)
        | otherwise -> Left (UnknownTypeReference tyName)
      TyRefFunc a b -> FuncTy <$> go a <*> go b
      TyRefPair a b -> PairTy <$> go a <*> go b
      TyRefSum a b -> SumTy <$> go a <*> go b
      TyRefBool -> pure BoolTy
      TyRefUnit -> pure UnitTy
      TyRefVoid -> pure VoidTy
      TyRefNatural -> pure NaturalTy
      TyRefInteger -> pure IntegerTy
      TyRefReal -> pure RealTy
      TyRefRecord fields -> RecordTy <$> traverse (traverse go) fields

-- | Look up a data type's spec by name. Returns 'Nothing' if the name is
-- unbound or refers to a term definition rather than a data type.
lookupType :: TyCnstrName -> AdtIndex -> Maybe DataTypeSpec
lookupType tyName AdtIndex {..} = do
  lvl <- Map.lookup tyName byType
  Map.lookup lvl specs >>= \case
    Data dtSpec -> pure dtSpec
    Defn _ _ -> Nothing

-- | Look up a data constructor by name, returning its owning type and
-- spec. Returns 'Nothing' if no data type declares it.
lookupCnstr :: DtCnstrName -> AdtIndex -> Maybe (TyCnstrName, DataConstructorSpec)
lookupCnstr dtName AdtIndex {..} = do
  lvl <- Map.lookup dtName byCnstr
  Map.lookup lvl specs >>= \case
    Data (DataTypeSpec tyName dtSpecs) -> do
      dtSpec <- find (\(Constr dtName' _ _) -> dtName == dtName') dtSpecs
      pure (tyName, dtSpec)
    Defn _ _ -> Nothing

-- | Look up a constructor by name within a specific data type. Returns
-- 'Nothing' when that type declares no constructor of the name, which is
-- how constructor membership is checked.
lookupCnstrInType :: TyCnstrName -> DtCnstrName -> AdtIndex -> Maybe DataConstructorSpec
lookupCnstrInType tyName dtName adtIndex = do
  (DataTypeSpec _ cnstrs) <- lookupType tyName adtIndex
  find (\(Constr dtName' _ _) -> dtName == dtName') cnstrs

-- | We predefine a few ADTs here for demonstration purposes. In a complete
-- language these would be defined using 'data' declarations in a module.
stockADTs :: AdtIndex
stockADTs =
  fromRight (error "Impossible! Invalid data type spec") $
    elaborateDefinitions
      [ DataDecl "MaybeBool" [CnstrDecl "Nothing" [], CnstrDecl "Just" [TyRefBool]],
        DataDecl "ListBool" [CnstrDecl "Nil" [], CnstrDecl "Cons" [TyRefBool, TyRef "ListBool"]],
        DataDecl "Fn" [CnstrDecl "MkFn" [TyRefFunc TyRefBool TyRefBool]]
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
    cellType :: Type,
    cellValue :: Value
  }
  deriving stock (Show, Eq, Ord)

-- | The typechecker/elaboration context.
--
-- @locals@ is the evaluator's environment (values by de Bruijn index),
-- @localNames@ is for name resolution (searched linearly), and @size@ tracks
-- the current binding depth (used to generate fresh de Bruijn levels).
data TypeCheckEnv = TypeCheckEnv
  { locals :: SnocList Value,
    localNames :: [Cell],
    size :: Int,
    -- | Holes encountered during typechecking
    holes :: [Type],
    -- | Stock ADTs
    adtEnv :: AdtIndex
  }
  deriving stock (Show, Eq, Ord)

-- | The evaluator's environment. Carries two independent snoc lists: one for
-- term variable bindings ('Value') and one for type variable bindings
-- ('VType'). The lengths track the current depth in each index space. Used both
-- as the top-level eval environment and captured inside closures.
data EvalEnv = EvalEnv
  { -- | Term variable bindings, indexed by de Bruijn index.
    envValues :: SnocList Value,
    envAdtEnv :: AdtIndex
  }
  deriving stock (Show, Eq, Ord)

-- | Project the evaluator environment from the typechecker context. The
-- typechecker carries extra metadata (names, holes, ADT specs) that the
-- evaluator does not need.
toEvalEnv :: TypeCheckEnv -> EvalEnv
toEvalEnv env =
  EvalEnv
    { envValues = env.locals,
      envAdtEnv = env.adtEnv
    }

initEnv :: TypeCheckEnv
initEnv = TypeCheckEnv Nil [] 0 mempty stockADTs

extendLocalNames :: TypeCheckEnv -> Cell -> TypeCheckEnv
extendLocalNames e@TypeCheckEnv {localNames} cell = e {localNames = cell : localNames}

extendHoles :: Type -> TypeCheckEnv -> TypeCheckEnv
extendHoles ty e@TypeCheckEnv {holes} = e {holes = ty : holes}

bindCell :: Cell -> TypeCheckEnv -> TypeCheckEnv
bindCell cell@Cell {..} TypeCheckEnv {..} =
  TypeCheckEnv
    { locals = Snoc locals cellValue,
      localNames = cell : localNames,
      size = size + 1,
      holes = holes,
      adtEnv = adtEnv
    }

resolveCell :: TypeCheckEnv -> Name -> Maybe Cell
resolveCell TypeCheckEnv {..} bndr = find ((== bndr) . cellName) localNames

-- | Create a fresh neutral variable at the current depth. Used for lambda-bound
-- variables where we don't know the value.
freshVar :: TypeCheckEnv -> Type -> Value
freshVar TypeCheckEnv {size} ty = VNeutral ty $ Neutral (VVar $ Lvl size) Nil

-- | Create a fresh cell for a lambda-bound variable. The value is a neutral
-- because we don't know the argument yet.
freshCell :: TypeCheckEnv -> Name -> Type -> Cell
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
  deriving (Show)

-- | Accumulated hole types from typechecking. Each time the typechecker
-- encounters a 'Hole' in check position, it 'tell's the expected type here.
newtype Holes = Holes {getHoles :: [Type]}
  deriving newtype (Show, Semigroup, Monoid)

newtype TypecheckM a = TypecheckM {runTypecheckM :: TypeCheckEnv -> (Either Error a, Holes)}
  deriving
    (Functor, Applicative, Monad, MonadReader TypeCheckEnv, MonadError Error, MonadWriter Holes)
    via (ExceptT Error (WriterT Holes (Reader TypeCheckEnv)))

newtype Check = Check {runCheck :: Type -> TypecheckM Syntax}

newtype Synth = Synth {runSynth :: TypecheckM (Type, Syntax)}

synth :: Term -> Synth
synth = \case
  Var bndr -> varTactic bndr
  Ap tm1 tm2 -> lamElim (synth tm1) (check tm2)
  Anno ty tm -> annoTactic ty (check tm)
  Hole -> Synth $ throwError $ TypeError "Cannot sythesize holes"
  Fst tm -> pairElimFst (synth tm)
  Snd tm -> pairElimSnd (synth tm)
  Get name tm -> recordElim name (synth tm)
  tm -> Synth $ throwError $ TypeError $ "Cannot synthesize type for " <> show tm

check :: Term -> Check
check (Lam bndr body) = lamIntro bndr (check body)
check (Let bndr e body) = letTactic bndr (synth e) (check body)
check Hole = holeTactic
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
-- (x : A) ∈ Γ
-- ─────────── Var⇒
--  Γ ⊢ x ⇒ A
varTactic :: Name -> Synth
varTactic bndr = Synth $ do
  ctx <- ask

  case resolveCell ctx bndr of
    Just Cell {..} -> do
      let quoted = flip runEvalM (toEvalEnv ctx) $ quote (Lvl $ size ctx) cellType cellValue
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
  tm <- check ty
  pure (ty, tm)

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
  a `FuncTy` b -> do
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
      (a `FuncTy` b, f) -> do
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
  PairTy a b -> do
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
      (PairTy ty1 _ty2, tm) -> pure (ty1, SFst tm)
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
      (PairTy _ty1 ty2, tm) -> pure (ty2, SSnd tm)
      (ty, _) -> throwError $ TypeError $ "Couldn't match expected type Pair with actual type '" <> show ty <> "'"

-- | Bool-True Introduction
--
-- Checked against 'BoolTy' (or a supertype via subtyping).
--
-- ──────────────── True⇐
-- Γ ⊢ True ⇐ Bool
boolIntroTrue :: Check
boolIntroTrue = Check $ \case
  BoolTy -> pure STru
  ty | BoolTy `isSubtypeOf` ty -> pure STru
  ty -> throwError $ TypeError $ "'Bool' cannot be a subtype of '" <> show ty <> "'"

-- | Bool-False Introduction
--
-- Checked against 'BoolTy'. Elaborates to 'SFls' (or a supertype via subtyping).
--
-- ──────────────── False⇐
-- Γ ⊢ False ⇐ Bool
boolIntroFalse :: Check
boolIntroFalse = Check $ \case
  BoolTy -> pure SFls
  ty | BoolTy `isSubtypeOf` ty -> pure SFls
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
  tm1 <- checkT1 BoolTy
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
  UnitTy -> pure SUnit
  ty | UnitTy `isSubtypeOf` ty -> pure SUnit
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
    VoidTy -> pure $ SAbsurd ty scrut
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
  SumTy a _b -> SInL <$> check a
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
  SumTy _a b -> SInR <$> check b
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
    SumTy a b -> do
      f <- checkT1 (FuncTy a ty)
      g <- checkT2 (FuncTy b ty)
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
  NaturalTy ->
    if n >= 0
      then pure (SNatural n)
      else throwError $ TypeError "Naturals must be greater then or equal to zero."
  ty | NaturalTy `isSubtypeOf` ty -> pure (SNatural n)
  ty -> throwError $ TypeError $ "'Natural' cannot be a subtype of '" <> show ty <> "'"

-- | Integer Introduction
--
-- Checked against 'IntegerTy' (or a supertype via subtyping, e.g. 'RealTy').
--
-- ──────── ℤ⇐
-- Γ ⊢ z ⇐  ℤ
intIntro :: Integer -> Check
intIntro z = Check $ \case
  IntegerTy -> pure (SInteger z)
  ty | IntegerTy `isSubtypeOf` ty -> pure (SInteger z)
  ty -> throwError $ TypeError $ "'Integer' cannot be a subtype of '" <> show ty <> "'"

-- | Real Introduction
--
-- Checked against 'RealTy' (or a supertype via subtyping).
--
-- ───────── ℝ⇐
-- Γ ⊢ r ⇐ ℝ
realIntro :: Scientific -> Check
realIntro r = Check $ \case
  RealTy -> pure (SReal r)
  ty | RealTy `isSubtypeOf` ty -> pure (SReal r)
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
  RecordTy ty -> do
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
      (RecordTy fields, tm) ->
        case lookup name fields of
          Just ty -> pure (ty, SGet name tm)
          Nothing -> throwError $ TypeError $ "Record does not contain a field called " <> show name
      (ty, _) -> throwError $ TypeError $ "Expected a record type but got " <> show ty

-- | ADT Introduction
--
-- The basic concept here is that we:
-- 1. Decompose the expected type through function arrows to find the ADT
--    return type.
-- 2. Match the return type against @AdtTy tyName@.
-- 3. Lookup the constructor spec and build the full constructor function type.
-- 4. Eta-expand the constructor, check applied arguments against parameter
--    types, and fold applications over the expanded constructor.
--
-- Supports partial application: if fewer arguments are provided than
-- parameters, the unapplied suffix remains as function arrows in the
-- expected type. For example:
--
-- @Cons : Bool → ListBool → ListBool@ checks @Cons True@ against
-- @Bool → ListBool@ by eta-expanding to @λ.λ. Cons 1 0@ and applying
-- @True@ to the first parameter.
--
--   Γ ⊢ C : T₁ → ... → Tₙ → T   Γ ⊢ tᵢ ⇐ Tᵢ (i ∈ 1...m, m ≤ n)
-- ──────────────────────────────────────────────── Cnstr⇐
--   Γ ⊢ (λ[x₁...xₙ]. C x₁...xₙ) t₁...tₘ
--     ⇐ Tₘ₊₁ → ... → Tₙ → T
adtIntro :: DtCnstrName -> [Check] -> Check
adtIntro nm chks = Check $ \expectedTy -> do
  let (returnTy, _) = decomposeFunction expectedTy
  case returnTy of
    AdtTy tyName -> do
      adtMap <- asks adtEnv
      case lookupCnstrInType tyName nm adtMap of
        Just dtSpec -> do
          let constrTy = dtSpec.cnstrType
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

-- | Decompose a function into its return type and a list of its args.
decomposeFunction :: Type -> (Type, [Type])
decomposeFunction (FuncTy a b) = (a :) <$> decomposeFunction b
decomposeFunction ty = (ty, [])

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
-- > data ListBool = Nil | Cons Bool ListBool
--
-- we build an eliminator that takes one branch per data constructor and
-- returns a goal type A:
--
-- > list-bool-elim : A -> (Bool -> ListBool -> A) -> ListBool -> A
--
-- NOTE: The Nil branch ought to be @() -> A@ but that is isomorphic to
-- @A@ so we simplify it.
--
-- Each branch is a function from the constructor's fields to A. The
-- fields keep their declared types. This is a non-recursive case rather
-- than a fold: a recursive field (the second field of Cons) stays
-- ListBool, so the branch receives the substructure itself rather than
-- an already eliminated result. The goal type A is the type of each
-- branch body.
--
-- The core 'DataTypeSpec' for ListBool is:
--
-- > DataTypeSpec "ListBool"
-- >   [ Constr "Nil" [] (AdtTy "ListBool"),
-- >     Constr
-- >       "Cons"
-- >       [BoolTy, AdtTy "ListBool"]
-- >       (FuncTy BoolTy (FuncTy (AdtTy "ListBool") (AdtTy "ListBool")))
-- >   ]
--
-- For example:
--
-- > case xs of
-- >   Nil       -> False
-- >   Cons b bs -> b
--
-- with goal type Bool checks the Nil body against @Bool@ and the Cons
-- body against @Bool -> ListBool -> Bool@.
adtElim :: Synth -> [(DtCnstrName, Check)] -> Check
adtElim scrut cases = Check $ \motive -> do
  (scrutTy, scrut') <- runSynth scrut
  case scrutTy of
    AdtTy tyName -> do
      adtIndex <- asks adtEnv
      case lookupType tyName adtIndex of
        Just dtSpec -> do
          let branchTypes = Map.fromList $ caseBranchTypes motive dtSpec
              checks = Map.fromList cases
              alignCases = \case
                These ty chk -> runCheck chk ty
                This _ty -> throwError $ TypeError $ "Missing case for constructor of type '" <> show tyName <> "'"
                That _chk -> throwError $ TypeError $ "Extra case branch not in type '" <> show tyName <> "'"
          cases' <- Map.toList <$> alignWithM alignCases branchTypes checks
          pure $ SCase scrut' motive cases'
        Nothing -> throwError $ UnknownDataType tyName
    ty -> throwError $ TypeError $ "Expected an ADT type but got: " <> show ty

-- | The type a single case branch is checked against: each constructor
-- field becomes a function argument, ending in the goal type.
--
-- Recursive fields keep their data type (this is case analysis, not a fold).
constrBranchType :: Type -> DataConstructorSpec -> (DtCnstrName, Type)
constrBranchType motiveTy (Constr nm args _) =
  (nm, foldr FuncTy motiveTy args)

-- | The branch types for every constructor of a data type, used to check
-- each arm of a case expression.
caseBranchTypes :: Type -> DataTypeSpec -> [(DtCnstrName, Type)]
caseBranchTypes motiveTy (DataTypeSpec _ specs) = fmap (constrBranchType motiveTy) specs

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
isSubtypeOf :: Type -> Type -> Bool
isSubtypeOf s@FuncTy {} t@FuncTy {} = functionSubtype s t
isSubtypeOf s@RecordTy {} t@RecordTy {} = recordSubtype s t
isSubtypeOf NaturalTy IntegerTy = True
isSubtypeOf NaturalTy RealTy = True
isSubtypeOf IntegerTy RealTy = True
isSubtypeOf super sub = super == sub

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
functionSubtype :: Type -> Type -> Bool
functionSubtype (s1 `FuncTy` s2) (t1 `FuncTy` t2) =
  t1 `isSubtypeOf` s1 && s2 `isSubtypeOf` t2
functionSubtype _ _ = error "impossible case in functionSubtype"

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
recordSubtype :: Type -> Type -> Bool
recordSubtype (RecordTy s) (RecordTy t) =
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

eval :: Syntax -> EvalM Value
eval = \case
  SVar (Ix ix) -> do
    env <- ask
    pure $ fromMaybe (error "internal error") $ nth env.envValues ix
  SLam bndr body -> do
    env <- ask
    pure $ VLam bndr (Closure env body)
  SAp tm1 tm2 -> do
    fun <- eval tm1
    arg <- eval tm2
    doApply fun arg
  SHole ty -> pure $ VNeutral ty (Neutral (VHole ty) Nil)
  SPair tm1 tm2 -> do
    tm1' <- eval tm1
    tm2' <- eval tm2
    pure $ VPair tm1' tm2'
  SFst tm -> eval tm >>= doFst
  SSnd tm -> eval tm >>= doSnd
  STru -> pure VTru
  SFls -> pure VFls
  SIf p motive t1 t2 -> do
    p' <- eval p
    t1' <- eval t1
    t2' <- eval t2
    doIf p' motive t1' t2'
  SUnit -> pure VUnit
  SAbsurd ty tm -> do
    tm' <- eval tm
    doSumAbsurd tm' ty
  SInL tm -> VInL <$> eval tm
  SInR tm -> VInR <$> eval tm
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
  SCase scrut motive patterns -> doCase scrut motive patterns

doApply :: Value -> Value -> EvalM Value
doApply (VLam _ clo) arg = appTermClosure clo arg
doApply (VNeutral (FuncTy ty1 ty2) neu) arg = pure $ VNeutral ty2 (pushFrame neu (VApp ty1 arg))
doApply _ _ = error "impossible case in doApply"

doFst :: Value -> EvalM Value
doFst (VPair a _b) = pure a
doFst (VNeutral (PairTy a _) neu) = pure $ VNeutral a (pushFrame neu VFst)
doFst _ = error "impossible case in doFst"

doSnd :: Value -> EvalM Value
doSnd (VPair _a b) = pure b
doSnd (VNeutral (PairTy _ b) neu) = pure $ VNeutral b (pushFrame neu VSnd)
doSnd _ = error "impossible case in doSnd"

doSumCase :: Value -> Type -> Value -> Value -> EvalM Value
doSumCase (VInL v) _motive f _ = doApply f v
doSumCase (VInR v) _motive _ g = doApply g v
doSumCase (VNeutral (SumTy a b) neu) motive f g =
  pure $ VNeutral motive (pushFrame neu (VSumCase (FuncTy a motive) (FuncTy b motive) motive f g))
doSumCase _ _ _ _ = error "impossible case in doSumCase"

doSumAbsurd :: Value -> Type -> EvalM Value
doSumAbsurd (VNeutral _ neu) ty = pure $ VNeutral ty (pushFrame neu (VAbsurd ty))
doSumAbsurd _ _ = error "impossible case in doSumAbsurd"

doIf :: Value -> Type -> Value -> Value -> EvalM Value
doIf VTru _ t1 _ = pure t1
doIf VFls _ _ t2 = pure t2
doIf (VNeutral _ neu) motive t1 t2 = pure $ VNeutral motive (pushFrame neu (VIf motive t1 t2))
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
doCase :: Syntax -> Type -> [(DtCnstrName, Syntax)] -> EvalM Value
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

appTermClosure :: Closure -> Value -> EvalM Value
appTermClosure (Closure env body) v = local (const $ env {envValues = Snoc env.envValues v}) $ eval body

--------------------------------------------------------------------------------
-- Quoting
--
-- Quoting reads back a 'Value' into 'Syntax' (normal form). It is
-- type-directed, the type tells us how to handle each value.
--
-- At function types quoting eta-expands, so even a neutral gets wrapped in a
-- lambda. This ensures normal forms are fully eta-long, which means two terms
-- are beta-eta equal iff their normal forms are syntactically identical.
--
-- The 'Lvl' parameter tracks how many binders we've gone under, so we can
-- convert de Bruijn levels (stable under extension) back to de Bruijn indices
-- (what syntax uses).
--
-- Produces 'Syntax' rather than 'Term' since that's what the evaluator and
-- the output both use.

quote :: Lvl -> Type -> Value -> EvalM Syntax
quote l (FuncTy ty1 ty2) (VLam bndr clo@(Closure _env _body)) = do
  body <- bindVar ty1 l $ \v l' -> do
    clo <- appTermClosure clo v
    quote l' ty2 clo
  pure $ SLam bndr body
quote l (FuncTy ty1 ty2) f = do
  body <- bindVar ty1 l $ \v l' ->
    doApply f v >>= quote l' ty2
  pure $ SLam "_" body
quote l (PairTy ty1 ty2) (VPair tm1 tm2) = do
  tm1' <- quote l ty1 tm1
  tm2' <- quote l ty2 tm2
  pure $ SPair tm1' tm2'
quote _ _ VTru = pure STru
quote _ _ VFls = pure SFls
quote _ _ VUnit = pure SUnit
quote l (SumTy a _b) (VInL tm) = SInL <$> quote l a tm
quote l (SumTy _a b) (VInR tm) = SInR <$> quote l b tm
quote _ _ (VNatural n) = pure $ SNatural n
quote _ _ (VInteger z) = pure $ SInteger z
quote _ _ (VReal r) = pure $ SReal r
quote l ty (VRecord fields) = SRecord <$> traverse (traverse (quote l ty)) fields
quote l (AdtTy tyName) (VCnstr nm args) = do
  adtEnv <- asks envAdtEnv
  case lookupCnstrInType tyName nm adtEnv of
    Just dcSpec ->
      SCnstr nm <$> zipWithM (quote l) dcSpec.cnstrArgs args
    Nothing ->
      error "impossible case in quote: constructor not found in its data type"
quote l _ (VNeutral _ neu) = quoteNeutral l neu
quote _ ty tm = error $ "impossible case in quote:\n" <> show ty <> "\n" <> show tm

quoteLevel :: Lvl -> Lvl -> Ix
quoteLevel (Lvl l) (Lvl x) = Ix (l - (x + 1))

quoteNeutral :: Lvl -> Neutral -> EvalM Syntax
quoteNeutral l Neutral {..} = foldM (quoteFrame l) (quoteHead l head) spine

quoteHead :: Lvl -> Head -> Syntax
quoteHead l (VVar lvl) = SVar (quoteLevel l lvl)
quoteHead _ (VHole ty) = SHole ty

quoteFrame :: Lvl -> Syntax -> Frame -> EvalM Syntax
quoteFrame l tm = \case
  VApp ty arg -> SAp tm <$> quote l ty arg
  VFst -> pure $ SFst tm
  VSnd -> pure $ SSnd tm
  VIf ty t1 t2 -> liftA2 (SIf tm ty) (quote l ty t1) (quote l ty t2)
  VAbsurd ty -> pure $ SAbsurd ty tm
  VSumCase tyF tyG mot f g -> do
    f' <- quote l tyF f
    g' <- quote l tyG g
    pure $ SSumCase tm mot f' g'
  -- NOTE: This never get constructed. Do I need them in STLC?
  VGet name -> pure $ SGet name tm
  VCase (AdtTy scrut) mot cases -> do
    adtEnv <- asks envAdtEnv
    patterns' <- forM cases $ \(dtName, val) -> do
      case lookupCnstrInType scrut dtName adtEnv of
        Just dtSpec -> do
          let (cnstrName, patTy) = constrBranchType mot dtSpec
          syn <- quote l patTy val
          pure (cnstrName, syn)
        Nothing ->
          error "impossible case in quote: constructor not found in its data type"
    pure $ SCase tm mot patterns'
  VCase {} -> error "impossible case in quote: cannot quote VCase against a non AdtTy"

bindVar :: Type -> Lvl -> (Value -> Lvl -> a) -> a
bindVar ty lvl f =
  let v = VNeutral ty $ Neutral (VVar lvl) Nil
   in f v $ incLevel lvl

--------------------------------------------------------------------------------
-- Main

run :: Term -> Either (Error, Holes) (RunResult Syntax Type Syntax, Holes)
run term =
  case runTypecheckM (runSynth $ synth term) initEnv of
    (Left err, holes) -> Left (err, holes)
    (Right (type', syntax), holes) -> do
      let evalEnv = EvalEnv Nil stockADTs
          result = flip runEvalM evalEnv $ do
            value <- eval syntax
            quote initLevel type' value
      pure (RunResult syntax type' result, holes)

main :: IO ()
main = do
  let test = runTest run
      testErr = runTestErr run

  putStrLn "=== Nominal Inductive Types ==="
  putStrLn ""

  -- Lambda / application
  section "Lambda & Application"
  test
    "identity: (\\x. x) () ==> ()"
    ( Ap
        (Anno (UnitTy `FuncTy` UnitTy) (Lam "x" (Var "x")))
        Unit
    )
  test
    "const: (\\x. \\y. x) () () ==> ()"
    ( Ap
        ( Ap
            (Anno (UnitTy `FuncTy` (UnitTy `FuncTy` UnitTy)) (Lam "x" (Lam "_" (Var "x"))))
            Unit
        )
        Unit
    )
  test
    "not True ==> False"
    ( Ap
        (Anno (BoolTy `FuncTy` BoolTy) (Lam "x" (If (Var "x") Fls Tru)))
        (Anno BoolTy Tru)
    )
  putStrLn ""

  -- Pairs
  section "Pairs"
  test
    "fst (True, False) ==> True"
    (Fst (Anno (PairTy BoolTy BoolTy) (Pair Tru Fls)))
  test
    "snd (True, False) ==> False"
    (Snd (Anno (PairTy BoolTy BoolTy) (Pair Tru Fls)))
  putStrLn ""

  -- Sums
  section "Sums"
  test
    "case InL True of InL x -> x | InR y -> y ==> True"
    ( Anno
        BoolTy
        ( SumCase
            (Anno (SumTy BoolTy BoolTy) (InL Tru))
            ("x", Var "x")
            ("y", Var "y")
        )
    )
  test
    "case InR False of InL x -> x | InR y -> y ==> False"
    ( Anno
        BoolTy
        ( SumCase
            (Anno (SumTy BoolTy BoolTy) (InR Fls))
            ("x", Var "x")
            ("y", Var "y")
        )
    )
  putStrLn ""

  -- Booleans / If
  section "Booleans"
  test
    "if True then False else True ==> False"
    (Anno BoolTy (If Tru Fls Tru))
  test
    "if False then False else True ==> True"
    (Anno BoolTy (If Fls Fls Tru))
  putStrLn ""

  -- Records
  section "Records"
  test
    "get foo { foo = True, bar = () } ==> True"
    ( Get
        "foo"
        (Anno (RecordTy [("foo", BoolTy), ("bar", UnitTy)]) (Record [("foo", Tru), ("bar", Unit)]))
    )
  putStrLn ""

  -- Numeric subtyping
  section "Numeric Subtyping"
  test
    "Natural 42 as Integer"
    (Anno IntegerTy (Natural 42))
  test
    "Natural 42 as Real"
    (Anno RealTy (Natural 42))
  test
    "Integer -3 as Real"
    (Anno RealTy (Integer (-3)))
  putStrLn ""

  -- Record subtyping
  section "Record Subtyping"
  test
    "({ foo : Bool, bar : Unit, baz : Unit } -> Bool) applied to wider record"
    ( Ap
        ( Anno
            (RecordTy [("foo", BoolTy)] `FuncTy` BoolTy)
            (Lam "x" (Get "foo" (Var "x")))
        )
        (Anno (RecordTy [("foo", BoolTy), ("bar", UnitTy), ("baz", UnitTy)]) (Record [("foo", Tru), ("bar", Unit), ("baz", Unit)]))
    )
  putStrLn ""

  -- Constructor tests
  section "Construction"
  test
    "Nil"
    (Anno (AdtTy "ListBool") (Cnstr "Nil" []))
  test
    "Cons True Nil"
    (Anno (AdtTy "ListBool") (Cnstr "Cons" [Tru, Cnstr "Nil" []]))
  test
    "Cons True (Cons False Nil)"
    (Anno (AdtTy "ListBool") (Cnstr "Cons" [Tru, Cnstr "Cons" [Fls, Cnstr "Nil" []]]))
  test
    "Nothing"
    (Anno (AdtTy "MaybeBool") (Cnstr "Nothing" []))
  test
    "Just True"
    (Anno (AdtTy "MaybeBool") (Cnstr "Just" [Tru]))
  test
    "MkFn (\\x. x) at Fn"
    (Anno (AdtTy "Fn") (Cnstr "MkFn" [Lam "x" (Var "x")]))
  putStrLn ""

  -- Partial application of constructors
  section "Partial Application"
  test
    "fully unapplied Cons"
    (Anno (FuncTy BoolTy (FuncTy (AdtTy "ListBool") (AdtTy "ListBool"))) (Cnstr "Cons" []))
  test
    "partially applied Cons"
    (Anno (FuncTy (AdtTy "ListBool") (AdtTy "ListBool")) (Cnstr "Cons" [Tru]))
  test
    "partially applied Just"
    (Anno (FuncTy BoolTy (AdtTy "MaybeBool")) (Cnstr "Just" []))
  putStrLn ""

  -- Case elimination
  section "Case Elimination"
  test
    "case Nil of Nil -> True | Cons x xs -> False ==> True"
    ( Anno
        BoolTy
        ( Case
            (Anno (AdtTy "ListBool") (Cnstr "Nil" []))
            [("Nil", [], Tru), ("Cons", ["x", "xs"], Fls)]
        )
    )
  test
    "case (Cons True Nil) of Nil -> False | Cons x xs -> x ==> True"
    ( Anno
        BoolTy
        ( Case
            (Anno (AdtTy "ListBool") (Cnstr "Cons" [Tru, Cnstr "Nil" []]))
            [("Nil", [], Fls), ("Cons", ["x", "xs"], Var "x")]
        )
    )
  test
    "case (Cons False Nil) of Nil -> True | Cons x xs -> x ==> False"
    ( Anno
        BoolTy
        ( Case
            (Anno (AdtTy "ListBool") (Cnstr "Cons" [Fls, Cnstr "Nil" []]))
            [("Nil", [], Tru), ("Cons", ["x", "xs"], Var "x")]
        )
    )
  test
    "case Nothing of Nothing -> True | Just x -> x ==> True"
    ( Anno
        BoolTy
        ( Case
            (Anno (AdtTy "MaybeBool") (Cnstr "Nothing" []))
            [("Nothing", [], Tru), ("Just", ["x"], Var "x")]
        )
    )
  test
    "case (Just False) of Nothing -> True | Just x -> x ==> False"
    ( Anno
        BoolTy
        ( Case
            (Anno (AdtTy "MaybeBool") (Cnstr "Just" [Fls]))
            [("Nothing", [], Tru), ("Just", ["x"], Var "x")]
        )
    )
  putStrLn ""

  -- Nested case
  section "Nested / Recursive"
  test
    "case (Cons True (Cons False Nil)) of Nil -> Nil | Cons x xs -> xs ==> Cons False Nil"
    ( Anno
        (AdtTy "ListBool")
        ( Case
            (Anno (AdtTy "ListBool") (Cnstr "Cons" [Tru, Cnstr "Cons" [Fls, Cnstr "Nil" []]]))
            [("Nil", [], Cnstr "Nil" []), ("Cons", ["x", "xs"], Var "xs")]
        )
    )
  test
    "case (case (Cons True (Cons False Nil)) of ... -> xs) of ... -> x ==> False"
    ( Anno
        BoolTy
        ( Case
            ( Anno
                (AdtTy "ListBool")
                ( Case
                    (Anno (AdtTy "ListBool") (Cnstr "Cons" [Tru, Cnstr "Cons" [Fls, Cnstr "Nil" []]]))
                    [("Nil", [], Cnstr "Nil" []), ("Cons", ["x", "xs"], Var "xs")]
                )
            )
            [("Nil", [], Tru), ("Cons", ["x", "xs"], Var "x")]
        )
    )
  putStrLn ""

  -- Case on a neutral scrutinee. These force doCase's VNeutral branch and
  -- the VCase quote arm, which the concrete-scrutinee tests above never
  -- reach. The case is kept in the normal form.
  section "Case: stuck on neutral scrutinee"
  test
    "\\xs. case xs of Nil -> True | Cons h t -> h"
    -- (λxs. case xs of Nil → True; Cons h t → h) : ListBool → Bool
    ( Anno
        (FuncTy (AdtTy "ListBool") BoolTy)
        (Lam "xs" (Case (Var "xs") [("Nil", [], Tru), ("Cons", ["h", "t"], Var "h")]))
    )
  test
    "\\m. case m of Nothing -> False | Just b -> b"
    -- (λm. case m of Nothing → False; Just b → b) : MaybeBool → Bool
    ( Anno
        (FuncTy (AdtTy "MaybeBool") BoolTy)
        (Lam "m" (Case (Var "m") [("Nothing", [], Fls), ("Just", ["b"], Var "b")]))
    )
  test
    "\\xs. case xs of Nil -> Nil | Cons h t -> t (motive is an ADT)"
    -- (λxs. case xs of Nil → Nil; Cons h t → t) : ListBool → ListBool
    ( Anno
        (FuncTy (AdtTy "ListBool") (AdtTy "ListBool"))
        (Lam "xs" (Case (Var "xs") [("Nil", [], Cnstr "Nil" []), ("Cons", ["h", "t"], Var "t")]))
    )
  putStrLn ""

  -- Holes
  section "Holes"
  test
    "identity with hole body"
    ( Anno
        (UnitTy `FuncTy` UnitTy)
        (Lam "x" Hole)
    )
  test
    "Cons ? Nil (hole in constructor arg)"
    (Anno (AdtTy "ListBool") (Cnstr "Cons" [Hole, Cnstr "Nil" []]))
  putStrLn ""

  -- Error cases
  section "Error Cases (expected failures)"
  testErr
    "Too many args: Cons True False Nil"
    (Anno (AdtTy "ListBool") (Cnstr "Cons" [Tru, Fls, Cnstr "Nil" []]))
  testErr
    "Unknown constructor"
    (Anno (AdtTy "ListBool") (Cnstr "Bogus" []))
  testErr
    "Constructor belongs to wrong ADT: Cons checked at MaybeBool (issue #23)"
    (Anno (AdtTy "MaybeBool") (Cnstr "Cons" [Tru]))
  testErr
    "Wrong ADT in recursive position: Nothing inside Cons (issue #23)"
    (Anno (AdtTy "ListBool") (Cnstr "Cons" [Tru, Cnstr "Nothing" []]))
  testErr
    "Type mismatch in constructor arg"
    (Anno (AdtTy "MaybeBool") (Cnstr "Just" [Unit]))
  testErr
    "Case on non-ADT type"
    ( Anno
        BoolTy
        (Case (Anno BoolTy Tru) [("Nil", [], Fls)])
    )
  testErr
    "Cannot synthesize lambda"
    (Lam "x" (Var "x"))
  testErr
    "Absurd on non-Void"
    ( Anno
        BoolTy
        (Absurd (Anno BoolTy Tru))
    )

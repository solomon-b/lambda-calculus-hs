{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- | Iso-Inductive Types, structural ADTs via fold\/unfold.
--
-- An alternative to nominal inductive types: a structural encoding using
-- iso-recursive types (@mu a. T@). Data type specs are compiled into mu-types
-- over nested sums of products: e.g. @data ListBool = Nil | Cons Bool ListBool@
-- becomes @mu L. Unit + (Bool * L)@. Constructor names are retained in the
-- surface syntax for ergonomics, but the core IR is purely structural.
-- Constructors implicitly fold and case expressions implicitly unfold, using
-- explicit 'SFold' and 'SUnfold'. Type-level substitution ('substTy') handles
-- unrolling by replacing the bound variable with the mu-type itself.
module Main where

--------------------------------------------------------------------------------

import Control.Arrow ((&&&))
import Control.Monad (foldM, forM, when)
import Control.Monad.Except (MonadError (..))
import Control.Monad.Identity
import Control.Monad.Reader (MonadReader (..), asks)
import Control.Monad.Trans.Except (ExceptT (..))
import Control.Monad.Trans.Reader (Reader, ReaderT (..))
import Control.Monad.Trans.Writer.Strict (WriterT (..))
import Control.Monad.Writer.Strict (MonadWriter (..))
import Data.Align (Semialign (..))
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

-- | Align two structures and traverse the result. Used by 'recordTactic' to
-- check term fields against type fields: 'These' means both present, 'This'
-- means a field in the type but not the term (missing), 'That' means a field in
-- the term but not the type (extra).
alignWithM :: (Traversable t, Applicative f, Semialign t) => (These a b1 -> f b2) -> t a -> t b1 -> f (t b2)
alignWithM f as = traverse f . align as

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
  | -- | A missing subterm. Can only appear in check position (where the
    -- expected type is known). In synth position it's an error.
    Hole
  | -- | Boolean true. @true@
    Tru
  | -- | Boolean false. @false@
    Fls
  | -- | Conditional. @if scrut then t else f@
    If Term Term Term
  | -- | A record literal: a list of named fields with values.
    Record [(Name, Term)]
  | -- | Field projection from a record.
    Get Name Term
  | -- | Void elimination. Can produce any type from a value of type 'Void',
    -- since no such value exists.
    Absurd Term
  | -- | Left injection into a sum type.
    InL Term
  | -- | Right injection into a sum type.
    InR Term
  | -- | Binary sum elimination. Binds a variable in each branch.
    SumCase Term (Name, Term) (Name, Term)
  | -- | An integer literal.
    Integer Integer
  | -- | A natural number literal.
    Natural Integer
  | -- | A real number literal.
    Real Scientific
  | -- | Apply a named data constructor. The constructor name is used to look up
    -- the 'DataTypeSpec' and derive the mu-type.
    Cnstr Name [Term]
  | -- | Pattern match on an iso-inductive type. Each branch names a
    -- constructor, binds its fields, and provides a body.
    CaseRec Term [(Name, [Name], Term)]
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
prettyTerm _ (Pair a b) =
  PP.tupled [prettyTerm lamPrec a, prettyTerm lamPrec b]
prettyTerm p (Fst e) =
  parensIf (p > appPrec) $
    "fst" PP.<+> prettyTerm atomPrec e
prettyTerm p (Snd e) =
  parensIf (p > appPrec) $
    "snd" PP.<+> prettyTerm atomPrec e
prettyTerm _ Unit = "()"
prettyTerm p (Anno ty e) =
  parensIf (p > lamPrec) $
    prettyTerm (lamPrec + 1) e PP.<+> ":" PP.<+> prettyType lamPrec ty
prettyTerm _ Hole = "_"
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
prettyTerm _ (Record fields) =
  PP.braces $
    PP.sep $
      PP.punctuate PP.comma $
        map (\(n, e) -> PP.pretty (getName n) PP.<+> "=" PP.<+> prettyTerm lamPrec e) fields
prettyTerm p (Get n e) =
  parensIf (p > appPrec) $
    prettyTerm atomPrec e <> "." <> PP.pretty (getName n)
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
prettyTerm _ (Integer n) = PP.pretty n
prettyTerm _ (Natural n) = PP.pretty n
prettyTerm _ (Real n) = PP.pretty (show n)
prettyTerm _ (Cnstr n []) = PP.pretty (getName n)
prettyTerm p (Cnstr n args) =
  parensIf (p > appPrec) $
    PP.pretty (getName n) PP.<+> PP.hsep (map (prettyTerm atomPrec) args)
prettyTerm p (CaseRec scrut branches) =
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

instance PP.Pretty Term where
  pretty = prettyTerm lamPrec

-- | The type language. Functions, pairs, unit, booleans, natural numbers, and
-- record types.
data Type
  = -- | Function type. @A -> B@.
    FuncTy Type Type
  | -- | Pair type. @A * B@.
    PairTy Type Type
  | -- | Unit type. @Unit@.
    UnitTy
  | -- | Bool Type. @Bool@.
    BoolTy
  | -- | A record type: a list of named fields with their types.
    RecordTy [(Name, Type)]
  | -- | Binary sum: @A + B@.
    SumTy Type Type
  | -- | The empty type. No values inhabit it.
    VoidTy
  | -- | Natural numbers. @Nat@. Subtype of 'IntegerTy'.
    NaturalTy
  | -- | Integers. @Int@. Subtype of 'RealTy'.
    IntegerTy
  | -- | Real numbers. @Real@. Top of the numeric tower.
    RealTy
  | -- | An iso-recursive type: @mu a. T@ where @a@ may appear in @T@ as a
    -- recursive reference. Unrolled by substituting the whole mu-type for @a@.
    MuTy Name Type
  | -- | A type variable, bound by 'MuTy'.
    TVar Name
  deriving stock (Show, Eq, Ord)

prettyType :: Prec -> Type -> PP.Doc ann
prettyType p (FuncTy a b) =
  parensIf (p > arrowPrec) $
    prettyType (arrowPrec + 1) a PP.<+> arrowSym PP.<+> prettyType arrowPrec b
prettyType p (PairTy a b) =
  parensIf (p > arrowPrec) $
    prettyType (arrowPrec + 1) a PP.<+> "*" PP.<+> prettyType arrowPrec b
prettyType _ UnitTy = "Unit"
prettyType _ BoolTy = "Bool"
prettyType _ (RecordTy fields) =
  PP.braces $
    PP.sep $
      PP.punctuate PP.comma $
        map (\(n, ty) -> PP.pretty (getName n) <> ":" PP.<+> prettyType lamPrec ty) fields
prettyType p (SumTy a b) =
  parensIf (p > sumPrec) $
    prettyType (sumPrec + 1) a PP.<+> "+" PP.<+> prettyType sumPrec b
prettyType _ VoidTy = "Void"
prettyType _ NaturalTy = "Nat"
prettyType _ IntegerTy = "Int"
prettyType _ RealTy = "Real"
prettyType p (MuTy n ty) =
  parensIf (p > lamPrec) $
    "μ" <> PP.pretty (getName n) <> "." PP.<+> prettyType lamPrec ty
prettyType _ (TVar n) = PP.pretty (getName n)

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
  | -- | Pair introduction.
    SPair Syntax Syntax
  | -- | First projection of a pair.
    SFst Syntax
  | -- | Second projection of a pair.
    SSnd Syntax
  | -- | The unit value.
    SUnit
  | -- | A hole carrying the expected type. Evaluates to a
    -- neutral so it propagates through NbE.
    SHole Type
  | -- | Boolean true.
    STru
  | -- | Boolean false.
    SFls
  | -- | Conditional. @if scrut then t else f@.
    SIf Syntax Type Syntax Syntax
  | -- | Record introduction. A list of named fields.
    SRecord [(Name, Syntax)]
  | -- | Record field projection. @r.field@.
    SGet Name Syntax
  | -- | Left injection into a sum type. @inl x@.
    SInL Syntax
  | -- | Right injection into a sum type. @inr x@.
    SInR Syntax
  | -- | Case analysis on a sum type. @case scrut of inl x -> l; inr y -> r@.
    SSumCase Syntax Type Syntax Syntax
  | -- | Elimination of the empty type. @absurd t@.
    SAbsurd Type Syntax
  | -- | An integer literal.
    SInteger Integer
  | -- | A natural number literal.
    SNatural Integer
  | -- | A real number literal.
    SReal Scientific
  | -- | Fold: wrap a value into a mu-type. Implicit in the surface syntax
    -- (constructors fold automatically).
    SFold Syntax
  | -- | Unfold: unwrap a mu-type to expose the inner sum of products. Implicit
    -- in the surface syntax (case expressions unfold automatically).
    SUnfold Syntax Type
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
  | -- | The unit value.
    VUnit
  | -- | Boolean true.
    VTru
  | -- | Boolean false.
    VFls
  | -- | An evaluated record.
    VRecord [(Name, Value)]
  | -- | Left injection value.
    VInL Value
  | -- | Right injection value.
    VInR Value
  | -- | An integer value.
    VInteger Integer
  | -- | A natural number value.
    VNatural Integer
  | -- | A real number value.
    VReal Scientific
  | -- | A folded value inside a mu-type. Unfolding extracts the inner value.
    VFold Value
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
  deriving newtype (Show, Eq, Ord)

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
  | -- | A stuck record projection.
    VGet Name
  | -- | A stuck case: the scrutinee is neutral.
    VSumCase Type Type Type Value Value
  | -- | A stuck absurd: the scrutinee is neutral at 'VoidTy'.
    VAbsurd Type
  | -- | A stuck unfold on a neutral mu-typed value.
    VUnfold Type
  deriving stock (Show, Eq, Ord)

pushFrame :: Neutral -> Frame -> Neutral
pushFrame Neutral {..} frame = Neutral {head = head, spine = Snoc spine frame}

-- | A closure pairs a function body with the environment it was defined in.
-- Instantiation extends the captured environment with the argument rather than
-- substituting. Closures also appear inside neutrals (as arguments in 'VApp'
-- frames).
data Closure = Closure {env :: SnocList Value, body :: Syntax}
  deriving stock (Show, Eq, Ord)

--------------------------------------------------------------------------------
-- ADTs

-- | A single data constructor: a name and a list of field types. Unlike module
-- 09, field types are plain 'Type' values (recursive references use 'TVar'
-- rather than a separate 'Rec' tag).
data DataConstructorSpec
  = Constr Name [Type]
  deriving stock (Show, Eq, Ord)

getCnstrName :: DataConstructorSpec -> Name
getCnstrName (Constr nm _) = nm

getCnstrTypes :: DataConstructorSpec -> [Type]
getCnstrTypes (Constr _ xs) = xs

-- | A complete data type definition. 'dataTypeSpecToMuTy' compiles this into an
-- iso-recursive mu-type over nested sums of products.
data DataTypeSpec = DataTypeSpec Name [DataConstructorSpec]
  deriving stock (Show, Eq, Ord)

-- | Compile a data type spec into a mu-type. Each constructor becomes a branch
-- of a nested sum, and its fields become a nested product. For example,
-- @ListBool@ with @Nil | Cons Bool ListBool@ becomes @mu L. Unit + (Bool * L)@.
dataTypeSpecToMuTy :: DataTypeSpec -> Type
dataTypeSpecToMuTy (DataTypeSpec tyName cnstrs) =
  MuTy tyName $ foldSums $ fmap (foldProducts . getCnstrTypes) cnstrs
  where
    foldProducts [] = UnitTy
    foldProducts [x] = x
    foldProducts (x : xs) = PairTy x (foldProducts xs)

    foldSums [] = VoidTy
    foldSums [x] = x
    foldSums (x : xs) = SumTy x (foldSums xs)

-- | We predefine a few ADTs here for demonstration purposes. In a complete
-- language these would be defined using 'data' declarations in a module.
stockADTs :: Map Name DataTypeSpec
stockADTs =
  Map.fromList
    [ ("MaybeBool", DataTypeSpec "MaybeBool" [Constr "Nothing" [], Constr "Just" [BoolTy]]),
      ("ListBool", DataTypeSpec "ListBool" [Constr "Nil" [], Constr "Cons" [BoolTy, TVar "ListBool"]])
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
data Env = Env
  { locals :: SnocList Value,
    localNames :: [Cell],
    size :: Int,
    -- | Holes encountered during typechecking
    holes :: [Type],
    -- | ADT Spec by Constructor Name
    adtConstructors :: Map Name DataTypeSpec
  }
  deriving stock (Show, Eq, Ord)

adtConstructorsMap :: Map Name DataTypeSpec
adtConstructorsMap = Map.fromList $ foldr (\d@(DataTypeSpec _ cs) acc -> fmap ((,d) . getCnstrName) cs <> acc) [] stockADTs

-- | Lookup a Data Constructor Spec from a Data Constructor Name.
lookupDataCnstrSpec :: Name -> ((Int, DataConstructorSpec) -> TypecheckM a) -> TypecheckM a
lookupDataCnstrSpec nm k =
  lookupDataTypeSpec nm $ \(DataTypeSpec tyName specs) ->
    case find (\(_, Constr nm' _) -> nm == nm') (zip [0 ..] specs) of
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
  case find (\(DataTypeSpec tyName' _) -> tyName == tyName') cnstrs of
    Just dataSpec -> k dataSpec
    Nothing -> throwError $ OutOfScopeError tyName

initEnv :: Env
initEnv = Env Nil [] 0 mempty adtConstructorsMap

extendLocalNames :: Env -> Cell -> Env
extendLocalNames e@Env {localNames} cell = e {localNames = cell : localNames}

extendHoles :: Type -> Env -> Env
extendHoles ty e@Env {holes} = e {holes = ty : holes}

bindCell :: Cell -> Env -> Env
bindCell cell@Cell {..} Env {..} =
  Env
    { locals = Snoc locals cellValue,
      localNames = cell : localNames,
      size = size + 1,
      holes = holes,
      adtConstructors = adtConstructors
    }

resolveCell :: Env -> Name -> Maybe Cell
resolveCell Env {..} bndr = find ((== bndr) . cellName) localNames

-- | Create a fresh neutral variable at the current depth. Used for lambda-bound
-- variables where we don't know the value.
freshVar :: Env -> Type -> Value
freshVar Env {size} ty = VNeutral ty $ Neutral (VVar $ Lvl size) Nil

-- | Create a fresh cell for a lambda-bound variable. The value is a neutral
-- because we don't know the argument yet.
freshCell :: Env -> Name -> Type -> Cell
freshCell ctx name ty = Cell name ty (freshVar ctx ty)

-- | Substitute a type for a named type variable throughout a type expression.
-- Used by 'unrollMuTy' to replace the bound variable with the mu-type itself.
substTy :: Name -> Type -> Type -> Type
substTy name replacement = go
  where
    go (TVar n) | n == name = replacement
    go (TVar n) = TVar n
    go (FuncTy a b) = FuncTy (go a) (go b)
    go (PairTy a b) = PairTy (go a) (go b)
    go (SumTy a b) = SumTy (go a) (go b)
    go (MuTy n t) | n == name = MuTy n t -- shadowed, don't recurse
    go (MuTy n t) = MuTy n (go t)
    go (RecordTy fields) = RecordTy (fmap (fmap go) fields)
    go t = t

-- | Unroll a μ-type by substituting the μ-type itself for the bound variable in
-- the body. For example:
--
-- unrollMuTy (μL. Unit + (Bool × L)) = Unit + (Bool × (μL. Unit + (Bool × L)))
unrollMuTy :: Type -> Type
unrollMuTy mu@(MuTy name body) = substTy name mu body
unrollMuTy ty = ty

-- | Weaken a 'Syntax' term by incrementing all free de Bruijn indices by one.
-- This is needed when pushing a term under an additional binder, such as the
-- lambdas introduced by 'buildCase' when elaborating n-ary case expressions
-- into nested binary sum eliminations.
weakenSyntax :: Syntax -> Syntax
weakenSyntax = go 0
  where
    go d (SVar (Ix i)) = SVar (Ix (if i >= d then i + 1 else i))
    go d (SLam n body) = SLam n (go (d + 1) body)
    go d (SAp a b) = SAp (go d a) (go d b)
    go d (SPair a b) = SPair (go d a) (go d b)
    go d (SFst a) = SFst (go d a)
    go d (SSnd a) = SSnd (go d a)
    go d (SInL a) = SInL (go d a)
    go d (SInR a) = SInR (go d a)
    go d (SSumCase s ty f g) = SSumCase (go d s) ty (go d f) (go d g)
    go d (SAbsurd ty s) = SAbsurd ty (go d s)
    go _ SUnit = SUnit
    go _ STru = STru
    go _ SFls = SFls
    go d (SIf p motive t f) = SIf (go d p) motive (go d t) (go d f)
    go d (SRecord fs) = SRecord (fmap (fmap (go d)) fs)
    go d (SGet n s) = SGet n (go d s)
    go _ (SInteger z) = SInteger z
    go _ (SNatural n) = SNatural n
    go _ (SReal r) = SReal r
    go d (SFold s) = SFold (go d s)
    go d (SUnfold s ty) = SUnfold (go d s) ty
    go _ (SHole ty) = SHole ty

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
--
-- The key additions: 'constructorTactic' synthesizes a constructor application
-- by looking up the data type spec, computing the mu-type, and elaborating to
-- 'SFold' with sum/product injections. 'caseRecTactic' checks a pattern match
-- by unfolding the mu-type and building nested binary sum eliminations.

data Error
  = TypeError String
  | OutOfScopeError Name
  deriving (Show)

-- | Accumulated hole types from typechecking. Each time the typechecker
-- encounters a 'Hole' in check position, it 'tell's the expected type here.
newtype Holes = Holes {getHoles :: [Type]}
  deriving newtype (Show, Semigroup, Monoid)

newtype TypecheckM a = TypecheckM {runTypecheckM :: Env -> (Either Error a, Holes)}
  deriving
    (Functor, Applicative, Monad, MonadReader Env, MonadError Error, MonadWriter Holes)
    via (ExceptT Error (WriterT Holes (Reader Env)))

newtype Check = Check {runCheck :: Type -> TypecheckM Syntax}

newtype Synth = Synth {runSynth :: TypecheckM (Type, Syntax)}

synth :: Term -> Synth
synth = \case
  Var bndr -> varTactic bndr
  Ap tm1 tm2 -> applyTactic (synth tm1) (check tm2)
  Fst tm -> fstTactic (synth tm)
  Snd tm -> sndTactic (synth tm)
  Anno ty tm -> annoTactic ty (check tm)
  Get name tm -> getTactic name (synth tm)
  Cnstr name tms -> constructorTactic name (fmap check tms)
  Hole -> Synth $ throwError $ TypeError "Cannot sythesize holes"
  tm -> Synth $ throwError $ TypeError $ "Cannot synthesize type for " <> show tm

check :: Term -> Check
check (Lam bndr body) = lamTactic bndr (check body)
check (Let bndr e body) = letTactic bndr (synth e) (check body)
check Unit = unitTactic
check (Pair tm1 tm2) = pairTactic (check tm1) (check tm2)
check (InL tm1) = inLTactic (check tm1)
check (InR tm2) = inRTactic (check tm2)
check (SumCase scrut (bndr1, t1) (bndr2, t2)) = sumCaseTactic (synth scrut) (check (Lam bndr1 t1)) (check (Lam bndr2 t2))
check (Absurd tm) = absurdTactic (synth tm)
check Hole = holeTactic
check (If tm1 tm2 tm3) = ifTactic (check tm1) (check tm2) (check tm3)
check Tru = trueTactic
check Fls = falseTactic
check (Integer z) = integerTactic z
check (Natural n) = naturalTactic n
check (Real r) = realTactic r
check (Record fields) = recordTactic (fmap (fmap (id &&& check)) fields)
check (CaseRec scrut cases) = caseRecTactic (synth scrut) (fmap (\(x, y, z) -> (x, check (foldr Lam z y))) cases)
check tm = subTactic (synth tm)

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
      let quoted = flip runEvalM (locals ctx) $ quote (Lvl $ size ctx) cellType cellValue
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
subTactic :: Synth -> Check
subTactic (Synth synth) = Check $ \ty1 -> do
  (ty2, tm) <- synth
  if ty2 `isSubtypeOf` ty1
    then pure tm
    else throwError $ TypeError $ "Type '" <> show ty2 <> "' cannot be a subtype of type '" <> show ty1 <> "'"

-- | Anno Tactic
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

-- | Unit Introduction Tactic
--
-- Verify the expected type is 'UnitTy' (or a supertype).
--
-- ───────────── Unit⇐
-- Γ ⊢ () ⇐ Unit
unitTactic :: Check
unitTactic = Check $ \case
  UnitTy -> pure SUnit
  ty | UnitTy `isSubtypeOf` ty -> pure SUnit
  ty -> throwError $ TypeError $ "'Unit' cannot be a subtype of '" <> show ty <> "'"

-- | Lambda Introduction Tactic
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
lamTactic :: Name -> Check -> Check
lamTactic bndr (Check bodyTac) = Check $ \case
  a `FuncTy` b -> do
    ctx <- ask
    let var = freshCell ctx bndr a
    fiber <- local (bindCell var) $ bodyTac b
    pure $ SLam bndr fiber
  ty -> throwError $ TypeError $ "Tried to introduce a lambda at a non-function type: " <> show ty

-- | Lambda Elimination Tactic
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
applyTactic :: Synth -> Check -> Synth
applyTactic (Synth funcTac) (Check argTac) =
  Synth $
    funcTac >>= \case
      (a `FuncTy` b, f) -> do
        arg <- argTac a
        pure (b, SAp f arg)
      (ty, _) -> throwError $ TypeError $ "Expected a function type but got " <> show ty

-- | Let Tactic
--
-- @let x = e in body@ elaborates to @(λx. body') e'@. There is no dedicated
-- @SLet@ in the core syntax. The let is fully dissolved by NbE: the beta redex
-- reduces and the bound value is inlined into the normal form.
--
-- Unlike 'lamTactic', which binds a fresh neutral variable (since the argument
-- is unknown), the let tactic evaluates @e@ and stores the resulting value in
-- the context cell. This means references to @x@ in the body see the actual
-- value during elaboration, not a stuck variable.
letTactic :: Name -> Synth -> Check -> Check
letTactic bndr (Synth synth) (Check bodyTac) = Check $ \ty -> do
  (ty1, tm1) <- synth
  ctx <- ask
  let val = runEvalM (eval tm1) (locals ctx)
      var = Cell bndr ty1 val
  fiber <- local (bindCell var) $ bodyTac ty
  pure $ SAp (SLam bndr fiber) tm1

-- | Pair Introduction Tactic
--
-- Like lambdas, pairs are checked. the expected pair type @A × B@ tells us what
-- to check each component against.
--
-- Elaborates to @SPair a' b'@.
--
-- Γ ⊢ a ⇐ A   Γ ⊢ b ⇐ B
-- ───────────────────── Pair⇐
--  Γ ⊢ (a , b) ⇐ A × B
pairTactic :: Check -> Check -> Check
pairTactic (Check checkFst) (Check checkSnd) = Check $ \case
  PairTy a b -> do
    tm1 <- checkFst a
    tm2 <- checkSnd b
    pure (SPair tm1 tm2)
  ty -> throwError $ TypeError $ "Couldn't match expected type Pair with actual type '" <> show ty <> "'"

-- | Pair Fst Elimination Tactic
--
-- Projection is a synth rule. Synthesize the pair's type to learn what the
-- components are, then return the appropriate one.
--
-- Γ ⊢ (t₁ , t₂) ⇒ A × B
-- ───────────────────── Fst⇒
--       Γ ⊢ t₁ ⇒ A
fstTactic :: Synth -> Synth
fstTactic (Synth synth) =
  Synth $
    synth >>= \case
      (PairTy ty1 _ty2, SPair tm1 _tm2) -> pure (ty1, tm1)
      (ty, _) -> throwError $ TypeError $ "Couldn't match expected type Pair with actual type '" <> show ty <> "'"

-- | Pair Snd Elimination Tactic
--
-- Same as fst, but returns the second component.
--
-- Γ ⊢ (t₁ , t₂) ⇒ A × B
-- ───────────────────── Snd⇒
--       Γ ⊢ t₂ ⇒ B
sndTactic :: Synth -> Synth
sndTactic (Synth synth) =
  Synth $
    synth >>= \case
      (PairTy _ty1 ty2, SPair _tm1 tm2) -> pure (ty2, tm2)
      (ty, _) -> throwError $ TypeError $ "Couldn't match expected type Pair with actual type '" <> show ty <> "'"

-- | Fold Introduction Tactic
--
-- Generally the fold introduction would be a Check rule:
--
-- Γ ⊢ e ⇐ T[μα.T / α]
-- ──────────────────── Fold⇐
-- Γ ⊢ fold e ⇐ μα.T
--
-- However, because the fold is implicit in our surface syntax because the
-- constructor name tells us the 'DataTypeSpec', giving us the @MuTy@. This
-- means the tactic is able to know the type and can check the arguments then
-- synthesize the results.
--
-- Γ ⊢ Cᵢ is the i-th constructor of D    D elaborates to μα.T
-- T[μα.T / α] = S₁ + (S₂ + ... + Sₙ)    Γ ⊢ args ⇐ Sᵢ
-- ──────────────────────────────────────────────────────── Cnstr⇒
--                    Γ ⊢ Cᵢ args ⇒ μα.T
constructorTactic :: Name -> [Check] -> Synth
constructorTactic nm checks = Synth $
  lookupDataTypeSpec nm $ \dataTy@(DataTypeSpec _ cnstrs) ->
    lookupDataCnstrSpec nm $ \(i, _dataConstrSpec) -> do
      let muTy = dataTypeSpecToMuTy dataTy
          unrolled = unrollMuTy muTy
          branchTy = nthSumBranch i unrolled
      tm <- checkArgs checks branchTy
      pure (muTy, SFold $ injectAt i (length cnstrs) tm)
  where
    nthSumBranch :: Int -> Type -> Type
    nthSumBranch 0 (SumTy a _b) = a
    nthSumBranch 0 ty = ty
    nthSumBranch n (SumTy _a b) = nthSumBranch (n - 1) b
    nthSumBranch _ _ = error "impossible: constructor index out of bounds"

    checkArgs [] UnitTy = pure SUnit
    checkArgs [c] ty = runCheck c ty
    checkArgs (c : cs) (PairTy a b) = do
      x <- runCheck c a
      xs <- checkArgs cs b
      pure (SPair x xs)
    checkArgs _cs _ty = throwError $ TypeError $ "Argument count mismatch for constructor '" <> show nm <> "'"

    injectAt :: Int -> Int -> Syntax -> Syntax
    injectAt 0 1 tm = tm
    injectAt 0 _ tm = SInL tm
    injectAt i n tm = SInR (injectAt (i - 1) (n - 1) tm)

-- | InL Introduction Tactic
--
-- Checked against a sum type. The payload is checked against the left
-- component.
--
--      Γ ⊢ e ⇐ A
--  ───────────────── InL⇐
--  Γ ⊢ InL e ⇐ A + B
inLTactic :: Check -> Check
inLTactic (Check check) = Check $ \case
  SumTy a _b -> SInL <$> check a
  ty -> throwError $ TypeError $ "Expected a Sum type but got: " <> show ty

-- | InR Introduction Tactic
--
-- Checked against a sum type. The payload is checked against the right
-- component.
--
--  Γ ⊢ e ⇐ B
--  ──────────────── InR⇐
--  Γ ⊢ InR e ⇐ A + B
inRTactic :: Check -> Check
inRTactic (Check check) = Check $ \case
  SumTy _a b -> SInR <$> check b
  ty -> throwError $ TypeError $ "Expected a Sum type but got: " <> show ty

-- | Sum Case Elimination Tactic
--
-- Synthesize the scrutinee's sum type, then check each branch as a
-- function from the injection's payload type to the motive. The
-- branches are elaborated as lambdas that bind the payload.
--
--  Γ ⊢ e ⇒ A + B    Γ ⊢ f ⇐ A → C    Γ ⊢ g ⇐ B → C
--  ─────────────────────────────────────────────── SumCase⇐
--                Γ ⊢ SumCase e f g ⇐ C
sumCaseTactic :: Synth -> Check -> Check -> Check
sumCaseTactic (Synth synth) (Check checkT1) (Check checkT2) = Check $ \ty -> do
  (scrutTy, scrut) <- synth
  case scrutTy of
    SumTy a b -> do
      f <- checkT1 (FuncTy a ty)
      g <- checkT2 (FuncTy b ty)
      pure $ SSumCase scrut ty f g
    _ -> throwError $ TypeError $ "Expected a Sum type but got: " <> show scrutTy

-- | Void Elimination Tactic
--
-- Synthesize the scrutinee and verify it has type 'VoidTy'. Since no value of
-- type 'Void' exists, this branch is unreachable, but it can produce any type
-- @C@.
--
--  Γ ⊢ e ⇒ Void
--  ─────────────── Absurd⇐
--  Γ ⊢ absurd e ⇐ C
absurdTactic :: Synth -> Check
absurdTactic (Synth synth) = Check $ \ty -> do
  (scrutTy, scrut) <- synth
  case scrutTy of
    VoidTy -> pure $ SAbsurd ty scrut
    _ -> throwError $ TypeError $ "Expected a Void but got: " <> show scrutTy

-- | Case-Rec Tactic
--
-- A typical Unfold tactic would look like:
--
--   Γ ⊢ e ⇒ μα.T
--  ──────────────────── Unfold
--  Γ ⊢ unfold e ⇒ T[μα.T / α]
--
-- However unfold never appears in our concrete syntax. It only appears as part
-- of our Case-Rec we do the unfold within the Case-Rec tactic:
--
--  Γ ⊢ e ⇒ μα.T    T[μα.T / α] = S₁ + (S₂ + ... + Sₙ)
--  Γ ⊢ fᵢ ⇐ Sᵢ → C   (for each i)
--  ──────────────────────────────────────── Case⇐
--  Γ ⊢ case e of C₁ → f₁ | ... | Cₙ → fₙ ⇐ C
caseRecTactic :: Synth -> [(Name, Check)] -> Check
caseRecTactic (Synth scrutinee) cases = Check $ \ty -> do
  (muTy, scrutinee) <- scrutinee
  case muTy of
    MuTy tyName _ -> do
      lookupDataTypeSpecByType tyName $ \(DataTypeSpec _ cnstrs) -> do
        let unrolled = unrollMuTy muTy
            casesMap = Map.fromList cases
            indexedCnstrs = zip [0 ..] cnstrs
        branches <- forM indexedCnstrs $ \(i, Constr name _) -> do
          case Map.lookup name casesMap of
            Just chk -> do
              let branchTy = nthSumBranch i unrolled
              tm <- runCheck chk (curryProductTy branchTy ty)
              pure (tm, branchTy)
            Nothing -> throwError $ TypeError $ "Missing case for constructor '" <> show name <> "'"
        when (Map.size casesMap > length cnstrs) $
          throwError $
            TypeError $
              "Extra case branches provided"

        pure $ buildCase (SUnfold scrutinee muTy) ty branches
    _ -> throwError $ TypeError $ "Expected a μ-type but got: " <> show muTy
  where
    nthSumBranch :: Int -> Type -> Type
    nthSumBranch 0 (SumTy a _b) = a
    nthSumBranch 0 ty = ty
    nthSumBranch n (SumTy _a b) = nthSumBranch (n - 1) b
    nthSumBranch _ _ = error "impossible: constructor index out of bounds"

    buildCase :: Syntax -> Type -> [(Syntax, Type)] -> Syntax
    buildCase scrut motive [] = SAbsurd motive scrut
    buildCase scrut _motive [(f, branchTy)] = uncurryApply f branchTy scrut
    buildCase scrut motive ((f, branchTy) : rest) =
      SSumCase
        scrut
        motive
        (SLam "_" (uncurryApply (weakenSyntax f) branchTy (SVar (Ix 0))))
        (SLam "_" (buildCase (SVar (Ix 0)) motive (fmap (\(s, t) -> (weakenSyntax s, t)) rest)))

    curryProductTy :: Type -> Type -> Type
    curryProductTy UnitTy motive = motive
    curryProductTy (PairTy a b) motive = FuncTy a (curryProductTy b motive)
    curryProductTy ty motive = FuncTy ty motive

    uncurryApply :: Syntax -> Type -> Syntax -> Syntax
    uncurryApply f UnitTy _scrut = f
    uncurryApply f (PairTy _a b) scrut = uncurryApply (SAp f (SFst scrut)) b (SSnd scrut)
    uncurryApply f _ty scrut = SAp f scrut

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
  tell (Holes [ty])
  pure (SHole ty)

-- | Bool-False Introduction Tactic
--
-- Checked against 'BoolTy'. Elaborates to 'SFls' (or a supertype via subtyping).
--
-- ──────────────── False⇐
-- Γ ⊢ False ⇐ Bool
falseTactic :: Check
falseTactic = Check $ \case
  BoolTy -> pure SFls
  ty | BoolTy `isSubtypeOf` ty -> pure SFls
  ty -> throwError $ TypeError $ "'Bool' cannot be a subtype of '" <> show ty <> "'"

-- | Bool-True Introduction Tactic
--
-- Checked against 'BoolTy' (or a supertype via subtyping).
--
-- ──────────────── True⇐
-- Γ ⊢ True ⇐ Bool
trueTactic :: Check
trueTactic = Check $ \case
  BoolTy -> pure STru
  ty | BoolTy `isSubtypeOf` ty -> pure STru
  ty -> throwError $ TypeError $ "'Bool' cannot be a subtype of '" <> show ty <> "'"

-- | Bool Elimination Tactic
--
-- Check the condition against 'BoolTy', and both branches against the expected
-- (motive) type. The motive is whatever type the @if@ expression is being
-- checked at. Elaborates to @SIf scrut' t' f'@.
--
-- Γ ⊢ t₁ ⇐ Bool  Γ ⊢ t₂ ⇐ T  Γ ⊢ t₃ ⇐ T
-- ───────────────────────────────────── If⇐
--   Γ ⊢ If t₁ then t₂ else t₃ ⇐ T
ifTactic :: Check -> Check -> Check -> Check
ifTactic (Check checkT1) (Check checkT2) (Check checkT3) = Check $ \ty -> do
  tm1 <- checkT1 BoolTy
  tm2 <- checkT2 ty
  tm3 <- checkT3 ty
  pure (SIf tm1 ty tm2 tm3)

-- | Record Introduction Tactic
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
recordTactic :: [(Name, (Term, Check))] -> Check
recordTactic fields = Check $ \case
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

-- | Record Elimination Tactic
--
-- Synthesize the record's type, then look up the projected field by name. A
-- synth rule because the record's type tells us the field's type.
--
-- Γ ⊢ t₁ ⇒ { lᵢ : Tᵢ (i ∈ I..n) }
-- ─────────────────────────────── Get⇒
--       Γ ⊢ Get lⱼ t₁ ⇒ Tⱼ
getTactic :: Name -> Synth -> Synth
getTactic name (Synth fieldTac) =
  Synth $
    fieldTac >>= \case
      (RecordTy fields, tm) ->
        case lookup name fields of
          Just ty -> pure (ty, SGet name tm)
          Nothing -> throwError $ TypeError $ "Record does not contain a field called " <> show name
      (ty, _) -> throwError $ TypeError $ "Expected a record type but got " <> show ty

-- | Integer Introduction Tactic
--
-- Checked against 'IntegerTy' (or a supertype via subtyping, e.g. 'RealTy').
--
-- ──────── ℤ⇐
-- Γ ⊢ z ⇐  ℤ
integerTactic :: Integer -> Check
integerTactic z = Check $ \case
  IntegerTy -> pure (SInteger z)
  ty | IntegerTy `isSubtypeOf` ty -> pure (SInteger z)
  ty -> throwError $ TypeError $ "'Integer' cannot be a subtype of '" <> show ty <> "'"

-- | Natural Introduction Tactic
--
-- Checked against 'NaturalTy' (or a supertype via subtyping, e.g. 'IntegerTy'
-- or 'RealTy'). Validates that the literal is non-negative.
--
-- ───────── ℕ⇐
-- Γ ⊢ n ⇐ ℕ
naturalTactic :: Integer -> Check
naturalTactic n = Check $ \case
  NaturalTy ->
    if n >= 0
      then pure (SNatural n)
      else throwError $ TypeError "Naturals must be greater then or equal to zero."
  ty | NaturalTy `isSubtypeOf` ty -> pure (SNatural n)
  ty -> throwError $ TypeError $ "'Natural' cannot be a subtype of '" <> show ty <> "'"

-- | Real Introduction Tactic
--
-- Checked against 'RealTy' (or a supertype via subtyping).
--
-- ───────── ℝ⇐
-- Γ ⊢ r ⇐ ℝ
realTactic :: Scientific -> Check
realTactic r = Check $ \case
  RealTy -> pure (SReal r)
  ty | RealTy `isSubtypeOf` ty -> pure (SReal r)
  ty -> throwError $ TypeError $ "'Real' cannot be a subtype of '" <> show ty <> "'"

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
isSubtypeOf s@RecordTy {} t@RecordTy {} = recordSubtypeTactic s t
isSubtypeOf s@FuncTy {} t@FuncTy {} = functionSubtypeTactic s t
isSubtypeOf NaturalTy IntegerTy = True
isSubtypeOf NaturalTy RealTy = True
isSubtypeOf IntegerTy RealTy = True
isSubtypeOf super sub = super == sub

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
recordSubtypeTactic :: Type -> Type -> Bool
recordSubtypeTactic (RecordTy s) (RecordTy t) =
  let s' = Map.fromList s
      t' = Map.fromList t
   in Map.isSubmapOfBy (flip isSubtypeOf) t' s'
recordSubtypeTactic _ _ = error "impossible case in rec"

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
functionSubtypeTactic :: Type -> Type -> Bool
functionSubtypeTactic (s1 `FuncTy` s2) (t1 `FuncTy` t2) =
  t1 `isSubtypeOf` s1 && s2 `isSubtypeOf` t2
functionSubtypeTactic _ _ = error "impossible case in functionSubTypeTactic"

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
--
-- 'SFold' evaluates to 'VFold'. 'SUnfold' on a 'VFold' extracts the inner
-- value; on a neutral it produces a stuck 'VUnfold' frame.

newtype EvalM a = EvalM {runEvalM :: SnocList Value -> a}
  deriving
    (Functor, Applicative, Monad, MonadReader (SnocList Value))
    via Reader (SnocList Value)

eval :: Syntax -> EvalM Value
eval = \case
  SVar (Ix ix) -> do
    env <- ask
    pure $ fromMaybe (error "internal error") $ nth env ix
  SLam bndr body -> do
    env <- ask
    pure $ VLam bndr (Closure env body)
  SAp tm1 tm2 -> do
    fun <- eval tm1
    arg <- eval tm2
    doApply fun arg
  SPair tm1 tm2 -> do
    tm1' <- eval tm1
    tm2' <- eval tm2
    pure $ VPair tm1' tm2'
  SFst tm -> eval tm >>= doFst
  SSnd tm -> eval tm >>= doSnd
  SInL tm -> eval tm >>= pure . VInL
  SInR tm -> eval tm >>= pure . VInR
  SSumCase t1 motive t2 t3 -> do
    t1' <- eval t1
    t2' <- eval t2
    t3' <- eval t3
    doSumCase t1' motive t2' t3'
  SAbsurd ty tm -> do
    tm' <- eval tm
    doSumAbsurd tm' ty
  SUnit -> pure VUnit
  STru -> pure VTru
  SFls -> pure VFls
  SIf p motive t1 t2 -> do
    p' <- eval p
    t1' <- eval t1
    t2' <- eval t2
    doIf p' motive t1' t2'
  SRecord fields -> doRecord fields
  SGet name tm -> eval tm >>= doGet name
  SInteger z -> pure $ VInteger z
  SNatural n -> pure $ VNatural n
  SReal r -> pure $ VReal r
  SFold tm -> VFold <$> eval tm
  SUnfold tm muTy -> eval tm >>= doUnfold muTy
  SHole ty -> pure $ VNeutral ty (Neutral (VHole ty) Nil)

doApply :: Value -> Value -> EvalM Value
doApply (VLam _ clo) arg = appTermClosure clo arg
doApply (VNeutral (FuncTy ty1 ty2) neu) arg = pure $ VNeutral ty2 (pushFrame neu (VApp ty1 arg))
doApply _ _ = error "impossible case in doApply"

doFst :: Value -> EvalM Value
doFst (VPair a _b) = pure a
doFst _ = error "impossible case in doFst"

doSnd :: Value -> EvalM Value
doSnd (VPair _a b) = pure b
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

doUnfold :: Type -> Value -> EvalM Value
doUnfold _ (VFold v) = pure v
doUnfold muTy (VNeutral _ neu) = pure $ VNeutral (unrollMuTy muTy) (pushFrame neu (VUnfold muTy))
doUnfold _ _ = error "impossible case in doUnfold"

appTermClosure :: Closure -> Value -> EvalM Value
appTermClosure (Closure env body) v = local (const $ Snoc env v) $ eval body

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
--
-- 'VFold' at 'MuTy' quotes by unrolling the mu-type and quoting the inner
-- value.

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
quote l (SumTy a _b) (VInL tm) = SInL <$> quote l a tm
quote l (SumTy _a b) (VInR tm) = SInR <$> quote l b tm
quote l _ (VNeutral _ neu) = quoteNeutral l neu
quote _ _ VUnit = pure SUnit
quote _ _ VTru = pure STru
quote _ _ VFls = pure SFls
quote l ty (VRecord fields) = SRecord <$> traverse (traverse (quote l ty)) fields
quote _ _ (VNatural n) = pure $ SNatural n
quote _ _ (VInteger z) = pure $ SInteger z
quote _ _ (VReal r) = pure $ SReal r
quote l (MuTy name body) (VFold v) = SFold <$> quote l (unrollMuTy (MuTy name body)) v
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
  VSumCase tyF tyG mot f g -> do
    f' <- quote l tyF f
    g' <- quote l tyG g
    pure $ SSumCase tm mot f' g'
  VAbsurd ty -> pure $ SAbsurd ty tm
  VIf ty t1 t2 -> liftA2 (SIf tm ty) (quote l ty t1) (quote l ty t2)
  -- NOTE: This never get constructed. Do I need them in STLC?
  VGet name -> pure $ SGet name tm
  VUnfold ty -> pure $ SUnfold tm ty

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
      let result = flip runEvalM Nil $ do
            value <- eval syntax
            quote initLevel type' value
      pure (RunResult syntax type' result, holes)

main :: IO ()
main = do
  let test = runTest run
      testErr = runTestErr run

  putStrLn "=== Iso-Inductive Types ==="
  putStrLn ""

  -- Construction tests
  section "Construction"
  test
    "Nil"
    (Cnstr "Nil" [])
  test
    "Cons True Nil"
    (Cnstr "Cons" [Tru, Cnstr "Nil" []])
  test
    "Cons True (Cons False Nil)"
    (Cnstr "Cons" [Tru, Cnstr "Cons" [Fls, Cnstr "Nil" []]])
  test
    "Nothing"
    (Cnstr "Nothing" [])
  test
    "Just True"
    (Cnstr "Just" [Tru])
  putStrLn ""

  -- Case elimination tests
  section "Case Elimination"
  test
    "case Nil of Nil -> True | Cons x xs -> False  ==>  True"
    ( Anno
        BoolTy
        ( CaseRec
            (Cnstr "Nil" [])
            [("Nil", [], Tru), ("Cons", ["x", "xs"], Fls)]
        )
    )
  test
    "case (Cons True Nil) of Nil -> False | Cons x xs -> x  ==>  True"
    ( Anno
        BoolTy
        ( CaseRec
            (Cnstr "Cons" [Tru, Cnstr "Nil" []])
            [("Nil", [], Fls), ("Cons", ["x", "xs"], Var "x")]
        )
    )
  test
    "case (Cons False Nil) of Nil -> True | Cons x xs -> x  ==>  False"
    ( Anno
        BoolTy
        ( CaseRec
            (Cnstr "Cons" [Fls, Cnstr "Nil" []])
            [("Nil", [], Tru), ("Cons", ["x", "xs"], Var "x")]
        )
    )
  test
    "case Nothing of Nothing -> True | Just x -> x  ==>  True"
    ( Anno
        BoolTy
        ( CaseRec
            (Cnstr "Nothing" [])
            [("Nothing", [], Tru), ("Just", ["x"], Var "x")]
        )
    )
  test
    "case (Just False) of Nothing -> True | Just x -> x  ==>  False"
    ( Anno
        BoolTy
        ( CaseRec
            (Cnstr "Just" [Fls])
            [("Nothing", [], Tru), ("Just", ["x"], Var "x")]
        )
    )
  putStrLn ""

  -- Nested case / recursive structure tests
  section "Nested / Recursive"
  let listBoolTy = dataTypeSpecToMuTy (DataTypeSpec "ListBool" [Constr "Nil" [], Constr "Cons" [BoolTy, TVar "ListBool"]])
  test
    "case (case (Cons True (Cons False Nil)) of Nil -> Nil | Cons x xs -> xs) of Nil -> True | Cons x xs -> x  ==>  False"
    ( Anno
        BoolTy
        ( CaseRec
            ( Anno
                listBoolTy
                ( CaseRec
                    (Cnstr "Cons" [Tru, Cnstr "Cons" [Fls, Cnstr "Nil" []]])
                    [("Nil", [], Cnstr "Nil" []), ("Cons", ["x", "xs"], Var "xs")]
                )
            )
            [("Nil", [], Tru), ("Cons", ["x", "xs"], Var "x")]
        )
    )
  test
    "case Nil of Nil -> Nil | Cons x xs -> xs  ==>  Nil (recursive return type)"
    ( Anno
        listBoolTy
        ( CaseRec
            (Cnstr "Nil" [])
            [("Nil", [], Cnstr "Nil" []), ("Cons", ["x", "xs"], Var "xs")]
        )
    )
  putStrLn ""

  -- Holes
  section "Holes"
  test
    "Cons ? Nil  (hole in constructor arg)"
    (Cnstr "Cons" [Hole, Cnstr "Nil" []])
  putStrLn ""

  -- Error cases
  section "Error Cases (expected failures)"
  testErr
    "Too many args: Cons True False Nil"
    (Cnstr "Cons" [Tru, Fls, Cnstr "Nil" []])
  testErr
    "Too few args: Cons True"
    (Cnstr "Cons" [Tru])
  testErr
    "Missing case branch"
    ( Anno
        BoolTy
        ( CaseRec
            (Cnstr "Nil" [])
            [("Nil", [], Tru)]
        )
    )
  testErr
    "Extra case branch"
    ( Anno
        BoolTy
        ( CaseRec
            (Cnstr "Nil" [])
            [("Nil", [], Tru), ("Cons", ["x", "xs"], Fls), ("Bogus", [], Fls)]
        )
    )
  testErr
    "Case on non-mu type"
    ( Anno
        BoolTy
        (CaseRec (Anno BoolTy Tru) [("Nil", [], Fls)])
    )
  testErr
    "Unknown constructor"
    (Cnstr "Bogus" [])

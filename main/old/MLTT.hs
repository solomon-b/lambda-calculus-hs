{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Main where

--------------------------------------------------------------------------------

import Control.Monad.State
import Data.Bool (bool)
import Data.Foldable (find, sequenceA_)
import Data.Maybe (fromMaybe)
import Data.String

--------------------------------------------------------------------------------
-- Utils

data SnocList a
  = Snoc (SnocList a) a
  | Nil
  deriving (Show, Eq, Ord, Functor, Foldable)

zipSnocWith :: (a -> b -> c) -> SnocList a -> SnocList b -> SnocList c
zipSnocWith f = go
  where
    go Nil _ = Nil
    go _ Nil = Nil
    go (Snoc as a) (Snoc bs b) = Snoc (go as bs) (f a b)

zipSnocWithM_ :: (Applicative m) => (a -> b -> m c) -> SnocList a -> SnocList b -> m ()
zipSnocWithM_ f xs ys = sequenceA_ (zipSnocWith f xs ys)

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
-- Environment

data Cell = Cell
  { cellName :: Name,
    cellType :: Value,
    cellValue :: Value
  }
  deriving stock (Show, Eq, Ord)

data Env = Env
  { locals :: SnocList Value,
    localNames :: [Cell],
    size :: Int
  }
  deriving stock (Show, Eq, Ord)

initEnv :: Env
initEnv = Env Nil [] 0

extendLocalNames :: Env -> Cell -> Env
extendLocalNames e@Env {localNames} cell = e {localNames = cell : localNames}

bindVar :: Env -> Cell -> Env
bindVar Env {..} cell@Cell {..} =
  Env
    { locals = Snoc locals cellValue,
      localNames = cell : localNames,
      size = size + 1
    }

--------------------------------------------------------------------------------
-- Terms

-- NOTE: 'ConcreteSyntax' would also contain spans if we were parsing.
data ConcreteSyntax
  = CSVar Name
  | CSPi Name ConcreteSyntax ConcreteSyntax
  | CSAbs Name ConcreteSyntax
  | CSApp ConcreteSyntax [ConcreteSyntax]
  | CSSigma Name ConcreteSyntax ConcreteSyntax
  | CSPair ConcreteSyntax ConcreteSyntax
  | CSFst ConcreteSyntax
  | CSSnd ConcreteSyntax
  | CSUnit
  | CSUnitTy
  | CSTrue
  | CSFalse
  | CSBoolTy
  | CSIf ConcreteSyntax ConcreteSyntax ConcreteSyntax ConcreteSyntax
  | CSAnno ConcreteSyntax ConcreteSyntax
  | CSHole
  | CSUniv
  deriving stock (Show, Eq, Ord)

data Syntax
  = SVar Ix
  | SPi Name Syntax Syntax
  | SAbs Name Syntax
  | SApp Syntax Syntax
  | SSigma Name Syntax Syntax
  | SPair Syntax Syntax
  | SFst Syntax
  | SSnd Syntax
  | SUnit
  | SUnitTy
  | STrue
  | SFalse
  | SBoolTy
  | -- | Motive Scrutinee Then Else
    SIf Syntax Syntax Syntax Syntax
  | SHole Syntax Int
  | SUniv
  deriving stock (Show, Eq, Ord)

data Value
  = VNeutral Value Neutral
  | VPi Name Value Closure
  | VLam Name Closure
  | VSigma Name Value Closure
  | VPair Value Value
  | VUnit
  | VUnitTy
  | VTrue
  | VFalse
  | VBoolTy
  | VUniv
  deriving stock (Show, Eq, Ord)

data Neutral = Neutral {head :: Head, spine :: SnocList Frame}
  deriving stock (Show, Eq, Ord)

data Head
  = VVar Lvl
  | VHole Value Int
  deriving (Show, Eq, Ord)

data Frame
  = -- | Type Arg
    VApp Value Value
  | VFst
  | VSnd
  | -- | Motive Then Else
    VIf Value Value Value
  deriving stock (Show, Eq, Ord)

pushFrame :: Neutral -> Frame -> Neutral
pushFrame Neutral {..} frame = Neutral {head = head, spine = Snoc spine frame}

data Closure = Closure {env :: SnocList Value, body :: Syntax}
  deriving stock (Show, Eq, Ord)

-- | Debruijn Indices
--
-- λ.λ.λ.2
-- ^-----^
newtype Ix
  = Ix Int
  deriving newtype (Show, Eq, Ord)

-- | Debruijn Levels
--
-- λ.λ.λ.0
-- ^-----^
newtype Lvl
  = Lvl Int
  deriving newtype (Show, Eq, Ord)

incLevel :: Lvl -> Lvl
incLevel (Lvl n) = Lvl (1 + n)

newtype Name = Name {getName :: String}
  deriving newtype (Show, Eq, Ord, IsString)

data Error
  = NotInScope Name
  | TypeError String
  | TypeHole Syntax
  | HoleInSynth
  deriving (Show)

--------------------------------------------------------------------------------
-- Typechecking

resolveCell :: Env -> Name -> Maybe Cell
resolveCell Env {..} bndr = find ((== bndr) . cellName) localNames

synth :: Env -> ConcreteSyntax -> Either Error (Value, Syntax) -- (Type × Term)
synth ctx = \case
  CSVar bndr ->
    case resolveCell ctx bndr of
      Just Cell {..} -> pure (cellType, quote (Lvl $ size ctx) cellType cellValue)
      Nothing -> Left $ NotInScope bndr
  CSUniv -> pure (VUniv, SUniv) -- Type is in type
  CSPi bndr a b -> do
    base <- check ctx a VUniv
    let vbase = eval (locals ctx) base
    let baseCell = freshCell ctx bndr vbase
    fam <- check (bindVar ctx baseCell) b VUniv
    pure (VUniv, SPi bndr base fam)
  CSApp f args -> do
    f' <- synth ctx f
    foldM (synAp ctx) f' args
  CSSigma bndr a b -> do
    base <- check ctx a VUniv
    let vbase = eval (locals ctx) base
    let baseCell = freshCell ctx bndr vbase
    fam <- check (bindVar ctx baseCell) b VUniv
    pure (VUniv, SSigma bndr base fam)
  CSFst a -> do
    synth ctx a >>= \case
      (VSigma _ a _clo, tm) ->
        pure (a, SFst tm)
      _ -> Left $ TypeError "Expected element of Σ."
  CSSnd a -> do
    synth ctx a >>= \case
      (VSigma _ _ clo, tm) ->
        let fiber = instantiateClosure clo $ doFst (eval (locals ctx) tm)
         in pure (fiber, SSnd tm)
      _ -> Left $ TypeError "Expected element of Σ."
  CSTrue -> pure (VBoolTy, STrue)
  CSFalse -> pure (VBoolTy, SFalse)
  CSUnit -> pure (VUnitTy, SUnit)
  CSUnitTy -> pure (VUniv, SUnitTy)
  CSBoolTy -> pure (VUniv, SBoolTy)
  CSIf mot scrut tru fls -> do
    -- check the motive against '(_ : Bool) → Univ'
    mot' <- check ctx mot $ VPi "_" VBoolTy $ Closure (locals ctx) SUniv
    -- evaluate the motive
    let vmot = eval (locals ctx) mot'
    -- check the true branch against 'motive True'
    tru' <- check ctx tru (doApply vmot VTrue)
    -- check the false branch against 'motive False'
    fls' <- check ctx fls (doApply vmot VFalse)
    -- synth the scrutinee
    (scrutTy, scrutTm) <- synth ctx scrut
    -- evaluate the scrutinee
    let vscrut = eval (locals ctx) scrutTm
    -- if the scrutinee is type 'Bool' then return:
    -- 1. The motive applied against the scrut to get the final returned type.
    -- 2. The normalized 'if' statement built from all the normalized components.
    case scrutTy of
      VBoolTy -> pure (doApply vmot vscrut, SIf mot' scrutTm tru' fls')
      _ -> Left $ TypeError $ "Scrutinee does not evaluate to a Bool: " <> show scrut
  CSAnno tm ty -> do
    ty' <- eval (locals ctx) <$> check ctx ty VUniv
    tm' <- check ctx tm ty'
    pure (ty', tm')
  CSHole -> Left HoleInSynth
  t -> Left $ TypeError $ "cannot synthesize type for: " <> show t

synAp :: Env -> (Value, Syntax) -> ConcreteSyntax -> Either Error (Value, Syntax)
synAp ctx (VPi _ a clo, f) arg = do
  arg' <- check ctx arg a
  let fiber = instantiateClosure clo (eval (locals ctx) arg')
  pure (fiber, SApp f arg')
synAp _ ty _ = Left $ TypeError $ "Not a function type: " <> show ty

check :: Env -> ConcreteSyntax -> Value -> Either Error Syntax
check ctx (CSAbs bndr body) ty =
  case ty of
    VPi _ a clo -> do
      let var = freshCell ctx bndr a
      let fiber = instantiateClosure clo a
      body <- check (bindVar ctx var) body fiber
      pure $ SAbs bndr body
    ty' -> Left $ TypeError $ "Abs requires a function type, but got a: " <> show ty'
check ctx (CSPair a b) ty =
  case ty of
    VSigma _ a' clo -> do
      t1 <- check ctx a a'
      t2 <- check ctx b $ instantiateClosure clo (eval (locals ctx) t1)
      pure $ SPair t1 t2
    _ -> Left $ TypeError "Expected element of Σ."
check ctx CSHole ty = do
  -- Note: For demonstration purposes here we simply return the first
  -- hole encountered. However, in a more complete system we would
  -- convert from a Concrete Syntax hole to a Syntax hole and have
  -- some effect to accumulate all the holes:

  -- label <- freshHole
  -- let hole = SHole ty label
  -- logHole hole
  -- pure hole

  -- This would allow us to continue typechecking and collect all the
  -- holes for reporting to the user. The required Hole constructors
  -- are included in our types to hint at this but the actual
  -- implementation is deferred so as to not obscure the core
  -- elaborator behavior.
  Left $ TypeHole $ quote (Lvl $ size ctx) ty VUniv
check ctx t1 goal = do
  (actual, tm) <- synth ctx t1
  case equate (size ctx) VUniv goal actual of
    Just _ -> pure tm
    Nothing -> Left $ TypeError $ "Expected type " <> show goal <> " but received " <> show actual

freshVar :: Int -> Value -> Value
freshVar size ty = VNeutral ty $ Neutral (VVar $ Lvl size) Nil

freshCell :: Env -> Name -> Value -> Cell
freshCell ctx name ty = Cell name ty (freshVar (size ctx) ty)

--------------------------------------------------------------------------------
-- Conversion Checker

equate :: Int -> Value -> Value -> Value -> Maybe ()
equate env _ (VNeutral _ neu1) (VNeutral _ neu2) = equateNeu env neu1 neu2
equate env _ (VPi _ a1 clo1) (VPi _ a2 clo2) = do
  equate env VUniv a1 a2
  let v = freshVar env a1
  equate (1 + env) VUniv (instantiateClosure clo1 v) (instantiateClosure clo2 v)
equate env (VPi _ a clo) v1 v2 = do
  let x = freshVar env a
      fiber = instantiateClosure clo x
  equate env fiber (doApply v1 x) (doApply v2 x)
equate env _ (VSigma _ a1 clo1) (VSigma _ a2 clo2) = do
  equate env VUniv a1 a2
  let v = freshVar env a1
  equate (1 + env) VUniv (instantiateClosure clo1 v) (instantiateClosure clo2 v)
equate env (VSigma _ a clo) v1 v2 = do
  equate env a (doFst v1) (doFst v2)
  let fiber = instantiateClosure clo v1
  equate env fiber (doSnd v1) (doSnd v2)
equate _ _ VUnit VUnit = pure ()
equate _ _ VTrue VTrue = pure ()
equate _ _ VFalse VFalse = pure ()
equate _ _ VBoolTy VBoolTy = pure ()
equate _ _ VUnitTy VUnitTy = pure ()
equate _ _ VUniv VUniv = pure ()
equate _ _ _ _ = Nothing

equateNeu :: Int -> Neutral -> Neutral -> Maybe ()
equateNeu env (Neutral hd1 frame1) (Neutral hd2 frame2) = do
  equateHead hd1 hd2
  zipSnocWithM_ (equateFrame env) frame1 frame2

equateHead :: Head -> Head -> Maybe ()
equateHead (VVar lvl1) (VVar lvl2) = bool Nothing (Just ()) (lvl1 == lvl2)
equateHead (VHole _ n) (VHole _ m) = bool Nothing (Just ()) (n == m)
equateHead _ _ = Nothing

equateFrame :: Int -> Frame -> Frame -> Maybe ()
equateFrame env (VApp ty1 arg1) (VApp _ arg2) = equate env ty1 arg1 arg2
equateFrame _ VFst VFst = pure ()
equateFrame _ VSnd VSnd = pure ()
equateFrame _ _ _ = Nothing

--------------------------------------------------------------------------------
-- Evaluation

eval :: SnocList Value -> Syntax -> Value
eval env = \case
  SVar (Ix ix) -> fromMaybe (error "internal error") $ nth env ix
  SPi bndr a b -> VPi bndr (eval env a) (Closure env b)
  SAbs bndr body -> VLam bndr (Closure env body)
  SApp t1 t2 ->
    let fun = eval env t1
        arg = eval env t2
     in doApply fun arg
  SSigma bndr a b -> VSigma bndr (eval env a) (Closure env b)
  SPair a b -> VPair (eval env a) (eval env b)
  SFst a -> doFst (eval env a)
  SSnd b -> doSnd (eval env b)
  STrue -> VTrue
  SFalse -> VFalse
  SUnit -> VUnit
  SUnitTy -> VUnitTy
  SBoolTy -> VBoolTy
  SIf mot scrut t2 t3 -> doIf (eval env mot) (eval env scrut) (eval env t2) (eval env t3)
  SHole ty ix ->
    let ty' = eval env ty
     in VNeutral ty' $ Neutral (VHole ty' ix) Nil
  SUniv -> VUniv

doApply :: Value -> Value -> Value
doApply (VLam _ clo) arg =
  instantiateClosure clo arg
doApply (VNeutral (VPi _ a clo) neu) arg =
  let fiber = instantiateClosure clo arg
   in VNeutral fiber (pushFrame neu (VApp a arg))
doApply _ _ = error "Internal Error: impossible case in doApply"

instantiateClosure :: Closure -> Value -> Value
instantiateClosure (Closure env body) v = eval (Snoc env v) body

doIf :: Value -> Value -> Value -> Value -> Value
doIf motive scrut t1 t2 =
  case scrut of
    VTrue -> t1
    VFalse -> t2
    VNeutral VBoolTy neu ->
      let fiber = doApply motive scrut
       in VNeutral fiber (pushFrame neu (VIf motive t1 t2))
    _ -> error "Internal Error: impossible case in doIf"

doFst :: Value -> Value
doFst (VPair a _b) = a
doFst (VNeutral (VSigma _ a _clo) neu) =
  VNeutral a (pushFrame neu VFst)
doFst _ = error "Internal Error: impossible case in doFst"

doSnd :: Value -> Value
doSnd (VPair _a b) = b
doSnd v@(VNeutral (VSigma _ _a clo) neu) =
  let fiber = instantiateClosure clo (doFst v)
   in VNeutral fiber (pushFrame neu VSnd)
doSnd _ = error "Internal Error: impossible case in doSnd"

quote :: Lvl -> Value -> Value -> Syntax
quote _ VUnitTy _ = SUnit
quote _ VBoolTy VTrue = STrue
quote _ VBoolTy VFalse = SFalse
quote l (VPi _ a cloTy) (VLam bndr clo) =
  let arg = VNeutral a $ Neutral (VVar l) Nil
      body = quote (incLevel l) (instantiateClosure cloTy arg) (instantiateClosure clo arg)
   in SAbs bndr body
quote l (VPi bndr a clo) v =
  let arg = VNeutral a $ Neutral (VVar l) Nil
      body = quote (incLevel l) (instantiateClosure clo arg) $ doApply v arg
   in SAbs bndr body
quote l _ (VPi bndr a clo) =
  let qa = quote l VUniv a
      arg = VNeutral a $ Neutral (VVar l) Nil
      b = quote (incLevel l) VUniv (instantiateClosure clo arg)
   in SPi bndr qa b
quote l _ (VSigma bndr a clo) =
  let qa = quote l VUniv a
      arg = VNeutral a $ Neutral (VVar l) Nil
      b = quote (incLevel l) VUniv (instantiateClosure clo arg)
   in SSigma bndr qa b
quote l (VSigma _bndr a clo) (VPair v1 v2) =
  let t1 = quote l a v1
      t2 = quote l (instantiateClosure clo v1) v2
   in SPair t1 t2
quote l (VSigma _bndr a clo) v =
  let v1 = doFst v
      t1 = quote l a v1
      t2 = quote l (instantiateClosure clo v1) (doSnd v)
   in SPair t1 t2
quote l ty1 (VNeutral ty2 neu) =
  if ty1 == ty2
    then quoteNeutral l neu
    else error "Internal error while quoting neutral"
quote _ _ VUnitTy = SUnitTy
quote _ _ VBoolTy = SBoolTy
quote _ _ VUniv = SUniv
quote _ _ v = error $ "Could not quote value: " <> show v

quoteLevel :: Lvl -> Lvl -> Ix
quoteLevel (Lvl l) (Lvl x) = Ix (l - (x + 1))

quoteNeutral :: Lvl -> Neutral -> Syntax
quoteNeutral l Neutral {..} = foldl (quoteFrame l) (quoteHead l head) spine

quoteHead :: Lvl -> Head -> Syntax
quoteHead l = \case
  VVar x -> SVar (quoteLevel l x)
  VHole ty ix -> (SHole (quote l VUniv ty) ix)

quoteFrame :: Lvl -> Syntax -> Frame -> Syntax
quoteFrame l t1 (VApp ty arg) = SApp t1 (quote l ty arg)
quoteFrame _ t1 VFst = SFst t1
quoteFrame _ t1 VSnd = SSnd t1
quoteFrame l t1 (VIf mot t2 t3) =
  SIf (quote l (VPi "_" VBoolTy $ Closure Nil SUniv) mot) t1 (quote l (doApply mot VTrue) t2) (quote l (doApply mot VFalse) t3)

normalize :: ConcreteSyntax -> Syntax
normalize term =
  case synth initEnv term of
    Right (ty, term') ->
      let val = eval Nil term'
       in quote (Lvl 0) ty val
    Left err -> error $ show err

--------------------------------------------------------------------------------
-- Prettyprinter

pp :: SnocList Name -> Syntax -> String
pp env = \case
  SVar (Ix ix) -> maybe ("![bad index " <> show ix <> "]!") getName $ nth env ix
  SPi bndr ty tm -> "( " <> getName bndr <> " : " <> pp env ty <> ") -> " <> pp (Snoc env bndr) tm
  SAbs bndr body -> "λ " <> getName bndr <> " . " <> pp (Snoc env bndr) body
  SApp t1 t2 -> pp env t1 <> " " <> pp env t2
  SSigma bndr a b -> "Σ[ " <> getName bndr <> " ∈ " <> pp env a <> " ] " <> pp (Snoc env bndr) b
  SPair a b -> pp env a <> " × " <> pp env b
  SFst a -> "fst " <> pp env a
  SSnd b -> "snd" <> pp env b
  STrue -> "True"
  SFalse -> "False"
  SUnit -> "Unit"
  SIf _ t1 t2 t3 -> "if " <> pp env t1 <> " then " <> pp env t2 <> " else " <> pp env t3
  SHole _ ix -> "_" <> show ix
  SBoolTy -> "Bool"
  SUnitTy -> "Unit"
  SUniv -> "Type"

--------------------------------------------------------------------------------
-- Main

-- | (A : Type) → (x : A) → A
idenT :: ConcreteSyntax
idenT =
  CSAnno
    (CSAbs "A" (CSAbs "x" (CSVar "x")))
    (CSPi "A" CSUniv (CSPi "x" (CSVar "A") (CSVar "A")))

-- | (A : Type) → (B : Type) → (x : A) → (y : B) → A
constT :: ConcreteSyntax
constT =
  CSAnno
    (CSAbs "A" (CSAbs "B" (CSAbs "x" (CSAbs "_" (CSVar "x")))))
    (CSPi "A" CSUniv (CSPi "B" CSUniv (CSPi "x" (CSVar "A") (CSPi "y" (CSVar "B") (CSVar "A")))))

-- | Bool → Bool
notT :: ConcreteSyntax
notT =
  CSAnno
    (CSAbs "p" (CSIf (CSAbs "x" CSBoolTy) (CSVar "p") CSFalse CSTrue))
    (CSPi "_" CSBoolTy CSBoolTy)

main :: IO ()
main = do
  let term = CSApp constT [CSBoolTy, CSUnitTy, CSTrue, CSUnit]
      term' = CSApp notT [CSFalse]
  case synth initEnv notT of
    Left err -> print err
    Right (ty, tm) -> do
      putStrLn $ "Type: " <> show ty
      putStrLn $ "Type Pretty: " <> pp Nil (quote (Lvl 0) VUniv ty)
      let val = eval Nil tm
      putStrLn ""
      putStrLn $ "Syntax: " <> show tm
      putStrLn $ "Syntax Pretty: " <> pp Nil tm
      putStrLn ""
      putStrLn $ "Value: " <> show val
      putStrLn $ "Quoted: " <> show (quote (Lvl 0) ty val)
      putStrLn $ "Quoted Pretty: " <> pp Nil (quote (Lvl 0) ty val)

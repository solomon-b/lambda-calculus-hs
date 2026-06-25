-- | A shared, datatype-agnostic suite of the foundation core tests.
--
-- Every module past the foundation redeclares its own @Term@/@Type@, so the
-- foundation tests cannot be imported as values. They can be shared as a
-- recipe: each module keeps the same surface constructors, so we abstract the
-- tests over a 'CoreVocab' record of those constructors and let each module
-- supply its own. 'foundationSuite' then runs the portable core tests against
-- any module that can fill the record, catching regressions as features are
-- added downstream.
--
-- Binders are taken as 'String'; each module's vocab wraps them in its own
-- @Name@. The surface type @ty@ is abstract too, so modules that collapse types
-- into terms (the dependent ones) instantiate it as their @Term@.
module FoundationSuite
  ( CoreVocab (..),
    foundationSuite,
  )
where

import Control.Monad (unless)
import PrettyTerm (Pretty)
import TestHarness (RunFn, ShowField, TestM, assertEval, section, testErr, testOk)

-- | The core surface vocabulary shared by the foundation and all later modules:
-- the simply typed lambda forms, pairs, binary sums, void, booleans, and their
-- type formers. Each field maps to a module's own constructor.
data CoreVocab term ty = CoreVocab
  { var :: String -> term,
    lam :: String -> term -> term,
    ap :: term -> term -> term,
    let_ :: String -> term -> term -> term,
    anno :: ty -> term -> term,
    hole :: term,
    pair :: term -> term -> term,
    fst_ :: term -> term,
    snd_ :: term -> term,
    inl :: term -> term,
    inr :: term -> term,
    sumCase :: term -> (String, term) -> (String, term) -> term,
    absurd :: term -> term,
    unit :: term,
    tru :: term,
    fls :: term,
    if_ :: term -> term -> term -> term,
    funcTy :: ty -> ty -> ty,
    pairTy :: ty -> ty -> ty,
    sumTy :: ty -> ty -> ty,
    boolTy :: ty,
    unitTy :: ty,
    voidTy :: ty
  }

-- | Run the portable foundation core tests against a module, using its runner
-- and its 'CoreVocab'. The @skip@ list names tests to omit (by label) for
-- modules where a test legitimately behaves differently; it is usually empty.
foundationSuite ::
  (Pretty term, Show elabTy, ShowField elab, ShowField val, Show norm, Eq norm, Show err) =>
  RunFn term err holes elab elabTy norm val ->
  [String] ->
  CoreVocab term ty ->
  TestM ()
foundationSuite run skip CoreVocab {..} = do
  let test l i e = unless (l `elem` skip) (assertEval run l i e)
      smoke l i = unless (l `elem` skip) (testOk run l i)
      err l i = unless (l `elem` skip) (testErr run l i)

  section "Foundation: Lambda & Application"
  test
    "identity: (\\x. x) () ==> ()"
    (ap (anno (funcTy unitTy unitTy) (lam "x" (var "x"))) unit)
    (anno unitTy unit)
  test
    "const: (\\x. \\y. x) () () ==> ()"
    (ap (ap (anno (funcTy unitTy (funcTy unitTy unitTy)) (lam "x" (lam "_" (var "x")))) unit) unit)
    (anno unitTy unit)
  test
    "not True ==> False"
    (ap (anno (funcTy boolTy boolTy) (lam "x" (if_ (var "x") fls tru))) (anno boolTy tru))
    (anno boolTy fls)
  -- The normal form is a lambda (eta expanded), whose binder names are not
  -- stable enough to assert against, so this stays a smoke test.
  smoke
    "id on functions: (\\f. f) : (Bool -> Bool) -> Bool -> Bool"
    (anno (funcTy (funcTy boolTy boolTy) (funcTy boolTy boolTy)) (lam "f" (var "f")))

  section "Foundation: Let Bindings"
  test
    "let x = True in (x, x) ==> (True, True)"
    (anno (pairTy boolTy boolTy) (let_ "x" tru (pair (var "x") (var "x"))))
    (anno (pairTy boolTy boolTy) (pair tru tru))
  test
    "let f = \\y. y in f () ==> ()"
    (anno unitTy (let_ "f" (lam "y" (var "y")) (ap (var "f") unit)))
    (anno unitTy unit)
  -- The two below annotate the bound value, so the binding's type comes from
  -- the annotation rather than inference. They hold even without unification.
  test
    "let x = (True : Bool) in x ==> True"
    (anno boolTy (let_ "x" (anno boolTy tru) (var "x")))
    (anno boolTy tru)
  test
    "let id = (\\y. y : Bool -> Bool) in id True ==> True"
    (anno boolTy (let_ "id" (anno (funcTy boolTy boolTy) (lam "y" (var "y"))) (ap (var "id") tru)))
    (anno boolTy tru)

  section "Foundation: Pairs"
  test
    "fst (True, False) ==> True"
    (fst_ (anno (pairTy boolTy boolTy) (pair tru fls)))
    (anno boolTy tru)
  test
    "snd (True, False) ==> False"
    (snd_ (anno (pairTy boolTy boolTy) (pair tru fls)))
    (anno boolTy fls)
  test
    "snd (snd (True, (Unit, False))) ==> False"
    (snd_ (snd_ (anno (pairTy boolTy (pairTy unitTy boolTy)) (pair tru (pair unit fls)))))
    (anno boolTy fls)

  section "Foundation: Sums"
  test
    "inl True : Bool + Unit ==> inl True"
    (anno (sumTy boolTy unitTy) (inl tru))
    (anno (sumTy boolTy unitTy) (inl tru))
  test
    "inr () : Bool + Unit ==> inr ()"
    (anno (sumTy boolTy unitTy) (inr unit))
    (anno (sumTy boolTy unitTy) (inr unit))
  test
    "case InL True of InL x -> x | InR y -> y ==> True"
    (anno boolTy (sumCase (anno (sumTy boolTy boolTy) (inl tru)) ("x", var "x") ("y", var "y")))
    (anno boolTy tru)
  test
    "case InR False of InL x -> x | InR y -> y ==> False"
    (anno boolTy (sumCase (anno (sumTy boolTy boolTy) (inr fls)) ("x", var "x") ("y", var "y")))
    (anno boolTy fls)
  smoke
    "\\s. case s of inl x -> x | inr y -> y (stuck on neutral s)"
    (anno (funcTy (sumTy boolTy boolTy) boolTy) (lam "s" (sumCase (var "s") ("x", var "x") ("y", var "y"))))

  section "Foundation: Booleans"
  test
    "if True then False else True ==> False"
    (anno boolTy (if_ tru fls tru))
    (anno boolTy fls)
  test
    "if False then False else True ==> True"
    (anno boolTy (if_ fls fls tru))
    (anno boolTy tru)
  smoke
    "\\b. if b then False else True (stuck on neutral b)"
    (anno (funcTy boolTy boolTy) (lam "b" (if_ (var "b") fls tru)))

  section "Foundation: Void"
  smoke
    "\\x. absurd x : Void -> Bool (stuck absurd)"
    (anno (funcTy voidTy boolTy) (lam "x" (absurd (var "x"))))

  section "Foundation: Error Cases (expected failures)"
  err
    "Cannot synthesize lambda"
    (lam "x" (var "x"))
  err
    "Absurd on non-Void"
    (anno boolTy (absurd (anno boolTy tru)))

  -- Holes and unification. These need metavariables, so a module that does not
  -- have unification yet skips these labels (along with the two inference lets
  -- above, which are also unification tests) until it gains it.
  section "Foundation: Holes"
  smoke
    "identity with hole body"
    (anno (funcTy unitTy unitTy) (lam "x" hole))

  section "Foundation: Unification (solvable holes)"
  smoke
    "bare _ synthesizes an unsolved metavariable"
    hole
  smoke
    "fst _ : the hole is forced to a pair skeleton"
    (fst_ hole)
  smoke
    "fst (snd _) : nested skeleton"
    (fst_ (snd_ hole))
  smoke
    "_ () : the hole is forced to a function"
    (ap hole unit)
  smoke
    "(_ () : Unit) pins the hole to Unit -> Unit"
    (anno unitTy (ap hole unit))
  smoke
    "case _ of InL/InR : scrutinee hole imitated to a sum"
    (anno boolTy (sumCase hole ("x", var "x") ("y", var "y")))
  smoke
    "_ (InL True) : domain imitated to a sum"
    (ap hole (inl tru))
  smoke
    "let x = _ in (x, True) : a use solves the hole to Bool"
    (anno (pairTy boolTy boolTy) (let_ "x" hole (pair (var "x") tru)))

  section "Foundation: Unification (expected failures)"
  err
    "(_, ()) : Bool : a pair cannot unify with Bool"
    (anno boolTy (pair hole unit))
  err
    "let x = _ in (x, x) : conflicting uses of the same hole"
    (anno (pairTy boolTy unitTy) (let_ "x" hole (pair (var "x") (var "x"))))
  err
    "let x = _ in x x : occurs check"
    (anno boolTy (let_ "x" hole (ap (var "x") (var "x"))))

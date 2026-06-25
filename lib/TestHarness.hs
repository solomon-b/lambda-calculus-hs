{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

-- | A small assertion based test harness shared across the executables.
--
-- Tests run in 'TestM', a state monad over 'IO' that accumulates a 'Summary'.
-- A passing test prints a single line; a failing test prints a debug block
-- (the pretty printed input, its type, the elaborated core, the evaluated
-- value, and the actual vs expected normal forms). Every test is isolated: a
-- pure exception thrown while forcing a result is caught and recorded as a
-- failure, so one crashing test never halts the rest of the run. 'runTests'
-- prints a tally of how many passed and failed (and which) at the end.
module TestHarness
  ( RunResult (..),
    ShowField (..),
    RunFn,
    TestM,
    runTests,
    assertEval,
    testOk,
    testErr,
    section,
  )
where

import Control.Exception (SomeException, evaluate, try)
import Control.Monad (unless)
import Control.Monad.State.Strict (StateT, liftIO, modify', runStateT)
import PrettyTerm (Pretty, pretty, render)

-- | A field that may or may not be worth displaying. The '()' instance hides
-- the field (returns 'Nothing'); everything else shows via its 'Show'.
class ShowField a where
  showField :: a -> Maybe String

instance ShowField () where
  showField () = Nothing

instance {-# OVERLAPPABLE #-} (Show a) => ShowField a where
  showField = Just . show

-- | The artifacts a module's runner produces for a single term: the elaborated
-- core, its type, the evaluated value, and the quoted normal form. The normal
-- form is what assertions compare on; the rest is for the failure debug block.
data RunResult elab ty norm val = RunResult
  { elaborated :: elab,
    elaboratedType :: ty,
    normalForm :: norm,
    value :: val
  }
  deriving stock (Show)

-- | A module's runner: elaborate and evaluate a term, or fail with an error.
-- The @holes@ payload rides along on both sides and is ignored by the harness.
type RunFn term err holes elab ty norm val =
  term -> Either (err, holes) (RunResult elab ty norm val, holes)

-- | Running tally of a test run.
data Summary = Summary
  { passed :: Int,
    failed :: [String]
  }

-- | Tests execute here, accumulating into the 'Summary'.
type TestM = StateT Summary IO

-- | Run a block of tests and print the final summary.
runTests :: TestM () -> IO ()
runTests block = do
  (_, s) <- runStateT block (Summary 0 [])
  printSummary s

printSummary :: Summary -> IO ()
printSummary (Summary p fs) = do
  let n = length fs
      total = p + n
  putStrLn ""
  putStrLn $ show p <> " passed, " <> show n <> " failed (of " <> show total <> ")"
  unless (null fs) $ do
    putStrLn "Failed:"
    mapM_ (\l -> putStrLn $ "  - " <> l) (reverse fs)

-- | A labelled group header.
section :: String -> TestM ()
section name = liftIO $ do
  putStrLn ""
  putStrLn $ "--- " <> name <> " ---"

-- | The verdict for a single test, with the debug lines to print on a failure.
data Outcome = Pass | Fail [String]

-- | Assert that @input@ and @expected@ normalize to the same thing. Both are
-- run through the same elaborate and evaluate pipeline, so @expected@ must
-- typecheck (carry its own annotation where needed).
assertEval ::
  (Pretty term, Show ty, ShowField elab, ShowField val, Show norm, Eq norm, Show err) =>
  RunFn term err holes elab ty norm val ->
  String ->
  term ->
  term ->
  TestM ()
assertEval run label input expected =
  record label $ case (run input, run expected) of
    (Left (err, _), _) -> Fail ["input rejected: " <> show err]
    (_, Left (err, _)) -> Fail ["expected term rejected: " <> show err]
    (Right (rIn, _), Right (rExp, _)) ->
      if normalForm rIn == normalForm rExp
        then Pass
        else Fail (failureDetail input rIn (normalForm rExp))

-- | Assert only that @input@ elaborates and evaluates without error. Useful
-- where there is no single clean expected value (e.g. a result that is still
-- an unsolved metavariable skeleton). The normal form is forced so an
-- evaluation crash is still caught.
testOk ::
  (Show norm, Show err) =>
  RunFn term err holes elab ty norm val ->
  String ->
  term ->
  TestM ()
testOk run label input =
  record label $ case run input of
    Left (err, _) -> Fail ["rejected: " <> show err]
    Right (rIn, _) -> let s = show (normalForm rIn) in length s `seq` Pass

-- | Assert that @input@ is rejected (the runner returns 'Left').
testErr ::
  (Show norm, Show err) =>
  RunFn term err holes elab ty norm val ->
  String ->
  term ->
  TestM ()
testErr run label input =
  record label $ case run input of
    Left _ -> Pass
    Right (rIn, _) -> Fail ["expected error but got: " <> show (normalForm rIn)]

-- | Force an outcome to normal form under an exception handler and record it.
-- Forcing the whole outcome here (the comparison and every debug line) is what
-- turns an evaluation crash into a failure instead of halting the run.
record :: String -> Outcome -> TestM ()
record label outcome = do
  forced <- liftIO $ try (evaluate (forceOutcome outcome))
  case forced of
    Left (e :: SomeException) -> recordFail label ["exception: " <> show e]
    Right Pass -> recordPass label
    Right (Fail detail) -> recordFail label detail

forceOutcome :: Outcome -> Outcome
forceOutcome Pass = Pass
forceOutcome (Fail ds) = sum (map length ds) `seq` Fail ds

recordPass :: String -> TestM ()
recordPass label = do
  liftIO $ putStrLn $ "  ok   " <> label
  modify' $ \s -> s {passed = passed s + 1}

recordFail :: String -> [String] -> TestM ()
recordFail label detail = do
  liftIO $ putStrLn $ "  FAIL " <> label
  liftIO $ mapM_ (putStrLn . ("       " <>)) detail
  modify' $ \s -> s {failed = label : failed s}

-- | The indented debug block shown when an assertion fails: the pretty printed
-- input, its type, the elaborated core, the evaluated value, and the actual vs
-- expected normal forms.
failureDetail ::
  (Pretty term, Show ty, ShowField elab, ShowField val, Show norm) =>
  term ->
  RunResult elab ty norm val ->
  norm ->
  [String]
failureDetail input rIn expNf =
  concat
    [ ["input:    " <> render (pretty input)],
      ["type:     " <> show (elaboratedType rIn)],
      maybe [] (\s -> ["elab:     " <> s]) (showField (elaborated rIn)),
      maybe [] (\s -> ["value:    " <> s]) (showField (value rIn)),
      ["actual:   " <> show (normalForm rIn)],
      ["expected: " <> show expNf]
    ]

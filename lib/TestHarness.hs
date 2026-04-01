module TestHarness
  ( RunResult (..),
    runTest,
    runTestErr,
    section,
  )
where

data RunResult ty syntax = RunResult
  { elaborated :: syntax,
    elaboratedType :: ty,
    normalForm :: syntax
  }
  deriving stock (Show)

runTest ::
  (Show term, Show ty, Show syntax, Show err) =>
  (term -> Either (err, holes) (RunResult ty syntax, holes)) ->
  String ->
  term ->
  IO ()
runTest run label term =
  case run term of
    Left (err, _) -> putStrLn $ "  FAIL: " <> label <> "\n        " <> show err
    Right (RunResult {..}, _) -> do
      putStrLn $ "  OK:   " <> label
      putStrLn $ "        Term:   " <> show term
      putStrLn $ "        Type:   " <> show elaboratedType
      putStrLn $ "        Elab:   " <> show elaborated
      putStrLn $ "        Normal: " <> show normalForm

runTestErr ::
  (Show err, Show syntax) =>
  (term -> Either (err, holes) (RunResult ty syntax, holes)) ->
  String ->
  term ->
  IO ()
runTestErr run label term =
  case run term of
    Left (err, _) -> putStrLn $ "  OK:   " <> label <> "\n        " <> show err
    Right (RunResult {..}, _) -> putStrLn $ "  FAIL: " <> label <> " (expected error but got result)\n        " <> show normalForm

section :: String -> IO ()
section name = putStrLn $ "--- " <> name <> " ---"

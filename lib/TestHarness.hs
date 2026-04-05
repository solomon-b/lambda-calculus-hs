{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module TestHarness
  ( RunResult (..),
    ShowField (..),
    runTest,
    runTestErr,
    section,
  )
where

import PrettyTerm (Pretty, pretty, render)

-- | A field that is present and should be displayed.
class ShowField a where
  showField :: a -> Maybe String

instance ShowField () where
  showField () = Nothing

instance {-# OVERLAPPABLE #-} (Show a) => ShowField a where
  showField = Just . show

data RunResult elab ty norm = RunResult
  { elaborated :: elab,
    elaboratedType :: ty,
    normalForm :: norm
  }
  deriving stock (Show)

runTest ::
  (Pretty term, Show term, Show ty, ShowField elab, ShowField norm, Show err) =>
  (term -> Either (err, holes) (RunResult elab ty norm, holes)) ->
  String ->
  term ->
  IO ()
runTest run label term =
  case run term of
    Left (err, _) -> putStrLn $ "  FAIL: " <> label <> "\n        " <> show err
    Right (RunResult {..}, _) -> do
      putStrLn $ "  OK:   " <> label
      putStrLn $ "        Term:   " <> render (pretty term)
      putStrLn $ "        Show:   " <> show term
      putStrLn $ "        Type:   " <> show elaboratedType
      mapM_ (\s -> putStrLn $ "        Elab:   " <> s) (showField elaborated)
      mapM_ (\s -> putStrLn $ "        Normal: " <> s) (showField normalForm)

runTestErr ::
  (Show err, ShowField norm) =>
  (term -> Either (err, holes) (RunResult elab ty norm, holes)) ->
  String ->
  term ->
  IO ()
runTestErr run label term =
  case run term of
    Left (err, _) -> putStrLn $ "  OK:   " <> label <> "\n        " <> show err
    Right (RunResult {..}, _) ->
      case showField normalForm of
        Just s -> putStrLn $ "  FAIL: " <> label <> " (expected error but got result)\n        " <> s
        Nothing -> putStrLn $ "  FAIL: " <> label <> " (expected error but got result)"

section :: String -> IO ()
section name = putStrLn $ "--- " <> name <> " ---"

{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
module Paths_SimplyTypedPresentation (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []
bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/home/solomon/.cabal/bin"
libdir     = "/home/solomon/.cabal/lib/x86_64-linux-ghc-8.6.5/SimplyTypedPresentation-0.1.0.0-inplace-SimplyTypedPresentation"
dynlibdir  = "/home/solomon/.cabal/lib/x86_64-linux-ghc-8.6.5"
datadir    = "/home/solomon/.cabal/share/x86_64-linux-ghc-8.6.5/SimplyTypedPresentation-0.1.0.0"
libexecdir = "/home/solomon/.cabal/libexec/x86_64-linux-ghc-8.6.5/SimplyTypedPresentation-0.1.0.0"
sysconfdir = "/home/solomon/.cabal/etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "SimplyTypedPresentation_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "SimplyTypedPresentation_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "SimplyTypedPresentation_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "SimplyTypedPresentation_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "SimplyTypedPresentation_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "SimplyTypedPresentation_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)

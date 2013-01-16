module Paths_hylores (
    version,
    getBinDir, getLibDir, getDataDir, getLibexecDir,
    getDataFileName
  ) where

import Data.Version (Version(..))
import System.Environment (getEnv)

version :: Version
version = Version {versionBranch = [2,5], versionTags = ["devel"]}

bindir, libdir, datadir, libexecdir :: FilePath

bindir     = "/Users/nevrenato/Library/Haskell/ghc-7.0.3/lib/hylores-2.5/bin"
libdir     = "/Users/nevrenato/Library/Haskell/ghc-7.0.3/lib/hylores-2.5/lib"
datadir    = "/Users/nevrenato/Library/Haskell/ghc-7.0.3/lib/hylores-2.5/share"
libexecdir = "/Users/nevrenato/Library/Haskell/ghc-7.0.3/lib/hylores-2.5/libexec"

getBinDir, getLibDir, getDataDir, getLibexecDir :: IO FilePath
getBinDir = catch (getEnv "hylores_bindir") (\_ -> return bindir)
getLibDir = catch (getEnv "hylores_libdir") (\_ -> return libdir)
getDataDir = catch (getEnv "hylores_datadir") (\_ -> return datadir)
getLibexecDir = catch (getEnv "hylores_libexecdir") (\_ -> return libexecdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)

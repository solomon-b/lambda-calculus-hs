-- This cabal.project contains some good defaults for profiling.
packages: lambda-calculus-hs.cabal

-- Enable profiling of local packages only; this avoids
-- bloating the output of the profiler.
profiling: True
profiling-detail: late-toplevel
optimization: 2

-- The usual parallelism flags
semaphore: True
jobs: $ncpus
        
package *
  -- Make the output of -hi useful.
  -- See https://downloads.haskell.org/ghc/latest/docs/users_guide/debug-info.html#ghc-flag-finfo-table-map
  ghc-options: -fdistinct-constructor-tables -finfo-table-map
 

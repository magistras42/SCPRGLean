#!/usr/bin/env bash
# Build and run the SymGC comparison (writeup.md §22.5).
#
# Vendored sources: LM18's own Haskell artifact, github.com/b5li/SymGC.
# Local additions:  Det.hs (the comparison driver).  See README.md for the
# four adaptations the vendored files needed to compile under modern GHC.
#
# Usage:  bash scratch/findings/symgc/build.sh
set -euo pipefail
cd "$(dirname "$0")"

# cabal writes .ghc.environment.*, which is how ghc finds these.  Idempotent.
if ! ls .ghc.environment.* >/dev/null 2>&1; then
  echo "== installing hashable, unordered-containers, QuickCheck =="
  cabal install --lib hashable unordered-containers QuickCheck --package-env .
fi

echo "== compiling =="
ghc -v0 -package containers -package mtl -o det Det.hs

echo "== running =="
./det

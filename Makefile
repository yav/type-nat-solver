# Change this to indicate what GHC is to be used.
GHC=${HOME}/src/ghc/master/inplace/bin/ghc-stage2

.PHONY: all test

all:
	cabal install -j1 -w ${GHC}

test:
	cabal install -j1 -w ${GHC} --enable-tests

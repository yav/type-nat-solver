# Change this to indicate what GHC is to be used.
GHC=ghc

.PHONY: all test

all:
	cabal install -j1 --disable-library-profiling -w ${GHC}

test:
	cabal install -j1 -w ${GHC} --enable-tests

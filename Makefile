GHC=/home/diatchki/src/ghc/master/inplace/bin/ghc-stage2

.PHONY: all test
all:
	cabal install -j1 -w ${GHC}

.PHONY: test
test:
	cabal install -j1 -w ${GHC} --enable-tests

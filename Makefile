GHC=/home/diatchki/src/ghc/master/inplace/bin/ghc-stage2

.PHONY: all
all:
	cabal install -w ${GHC} --enable-tests

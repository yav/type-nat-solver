{-# OPTIONS_GHC -fplugin=TypeNatSolver #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
module Examples where

import GHC.TypeLits
import Data.Proxy

data UNat :: Nat -> * where
  Zero :: UNat 0
  Succ :: UNat n -> UNat (n + 1)

uAdd :: UNat m -> UNat n -> UNat (m + n)
uAdd Zero x      = x
uAdd (Succ x) y  = Succ (uAdd x y)


data BNat :: Nat -> * where
  Empty :: BNat 0
  Even  :: (1 <= n) => BNat n -> BNat (2 * n)
  Odd   :: BNat n -> BNat (2 * n + 1)

bSucc :: BNat m -> BNat (m + 1)
bSucc Empty     = Odd Empty
bSucc (Even x)  = Odd x
bSucc (Odd x)   = Even (bSucc x)

bAdd :: BNat m -> BNat n -> BNat (m + n)
bAdd Empty x            = x
bAdd x Empty            = x
bAdd (Even x) (Even y)  = Even (bAdd x y)
bAdd (Even x) (Odd y)   = Odd  (bAdd x y)
bAdd (Odd x)  (Even y)  = Odd  (bAdd x y)
bAdd (Odd x)  (Odd  y)  = Even (bSucc (bAdd x y))



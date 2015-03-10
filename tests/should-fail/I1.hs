{-# OPTIONS_GHC -fplugin=TypeNatSolver #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
module I1 where

import GHC.TypeLits
import Data.Proxy

data Nat1 :: Nat -> * where
  Zero :: Nat1 0
  Succ :: Nat1 n -> Nat1 (n + 1)

add :: Nat1 m -> Nat1 n -> Nat1 (m + n + 1)
add Zero x      = x
add (Succ x) y  = Succ (add x y)



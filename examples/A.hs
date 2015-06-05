{-# OPTIONS_GHC -fplugin=TypeNatSolver #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
module A where

import GHC.TypeLits
import Data.Proxy

f :: ((a + 6) ~ x) => Proxy x -> ()
f = g

g :: ((6 <=? x) ~ True) => Proxy x -> ()
g _ = ()

data Vec :: Nat -> * -> * where
  Nil :: Vec 0 a
  Cons :: a -> Vec n a -> Vec (n + 1) a

vecHead :: Vec (n + 1) a -> a
vecHead (Cons x _) = x

vecZipWith :: (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
vecZipWith f Nil         Nil         = Nil
vecZipWith f (Cons x xs) (Cons y ys) = Cons (f x y) (vecZipWith f xs ys)

append :: Vec m a -> Vec n a -> Vec (n + m) a
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

reverse = go Nil
  where
  go :: Vec m a -> Vec n a -> Vec (m + n) a
  go xs Nil = xs
  go xs (Cons y ys) = go (Cons y xs) ys


f1 :: Proxy (2 + a) -> ()
f1 = g1

g1 :: Proxy (1 + a) -> ()
g1 _ = ()



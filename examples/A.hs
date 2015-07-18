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



vecMaximum :: Vec (n + 1) Int -> Int
vecMaximum (Cons x xs) = go x xs
  where
  go :: Int -> Vec a Int -> Int
  go m Nil         = m
  go m (Cons n xs) = go (max m n) xs

testLin :: Vec (2 + m) a -> a
testLin xs = vecHead xs


{-
-- XXX: Tricky, requires us to "invent" a new variable.
testLin :: (2 <= a) => Vec a Int -> Int
testLin xs = vecMaximum xs
-}

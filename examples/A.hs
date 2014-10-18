{-# OPTIONS_GHC -ftc-plugin=TypeNatSolver #-}
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

--{-
data Vec :: Nat -> * -> * where
  Nil :: Vec 0 a
  Cons :: a -> Vec n a -> Vec (n + 1) a


append :: Vec m a -> Vec n a -> Vec (n + m) a
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

reverse = go Nil
  where
  go :: Vec m a -> Vec n a -> Vec (m + n) a
  go xs Nil = xs
  go xs (Cons y ys) = go (Cons y xs) ys
--}

{-
f :: Proxy (2 + a) -> ()
f = g

g :: Proxy (1 + a) -> ()
g _ = ()
-}



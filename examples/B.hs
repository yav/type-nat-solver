{-# OPTIONS_GHC -ftc-plugin=TypeNatSolver #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
module B where

import GHC.TypeLits
import Data.Proxy

type family SomeFun (a :: Nat)

ti7 :: (x <= y, y <= x) => Proxy (SomeFun x) -> Proxy y -> ()
ti7 _ _ = ()


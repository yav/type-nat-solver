{-# OPTIONS_GHC -fplugin=TypeNatSolver #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
module I2 where

import GHC.TypeLits
import Data.Proxy

f :: Proxy (6 + x) -> ()
f x = g x

g :: (6 <= x) => Proxy x -> ()
g _ = ()




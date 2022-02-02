||| This module is based on the content of the functional pearl
||| How to Take the Inverse of a Type
||| by Daniel Marshall and Dominic Orchard

module Data.Linear.Diff

import Data.Linear
import Data.Linear.Inverse
import Data.Linear.LEither

%default total

public export
Quadruple : Type -> Type
Quadruple a = LPair a (LPair a (LPair a a))

-- Differentiating a⁴ wrt a gives us 4a³
data QuadContexts : Type -> Type where
  Mk1 : (1    y, z, w : a) -> QuadContexts a
  Mk2 : (1 x,    z, w : a) -> QuadContexts a
  Mk3 : (1 x, y,    w : a) -> QuadContexts a
  Mk4 : (1 x, y, z    : a) -> QuadContexts a

-- Differentiating a⁴ wrt a² gives us 4a³ * (2a)⁻¹
data QuadTwoContexts : Type -> Type where
  Mk : QuadContexts a -@ Inverse (LEither a a) -@ QuadTwoContexts a

-- Consume the element next to the hole such that the 2-hole
-- does not separate the remaining values of the original tuple
fromContext : LPair a a -@ QuadTwoContexts a -@ Quadruple a
fromContext (h1 # h2) (Mk (Mk1 y z w) inv)
  = (Right y `divide` inv) `seq` (h1 # h2 # z # w)
fromContext (h1 # h2) (Mk (Mk2 x z w) inv)
  = (Left x `divide` inv) `seq` (h1 # h2 # z # w)
fromContext (h1 # h2) (Mk (Mk3 x y w) inv)
  = (Right w `divide` inv) `seq` (x # y # h1 # h2)
fromContext (h1 # h2) (Mk (Mk4 x y z) inv)
  = (Left z `divide` inv) `seq` (x # y # h1 # h2)

-- The current hole in QuadTwoContexts is understood to be the
-- 2nd one placeholder for the fillers.
-- Always consume the element to the left of it to fit the 2-hole
-- (if none then throw the left hole away)
fromContext' : LPair a a -@ QuadTwoContexts a -@ Quadruple a
fromContext' (h1 # h2) (Mk (Mk1 y z w) inv)
  -- first hole outside of the tuple
  = (Left h1 `divide` inv) `seq` (h2 # y # z # w)
fromContext' (h1 # h2) (Mk (Mk2 x z w) inv)
  -- 2-hole at the start of the tuple
  = (Left x `divide` inv) `seq` (h1 # h2 # z # w)
fromContext' (h1 # h2) (Mk (Mk3 x y w) inv)
  -- 2-hole in the middle of the tuple
  = (Left y `divide` inv) `seq` (x # h1 # h2 # w)
fromContext' (h1 # h2) (Mk (Mk4 x y z) inv)
  -- 2-hole at the end of the tuple
  = (Left z `divide` inv) `seq` (x # y # h1 # h2)

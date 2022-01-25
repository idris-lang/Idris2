%default total

data TTy : Nat -> Nat -> Nat -> Nat -> Bool -> Type where

  TA : TTy p1 r1 i1 i2 False ->
       TTy i1 i2 i1 u2 False ->
       TTy i1 i2 p2 b1 b2    ->
       TTy p1 r1 p1 i2 False

  TB : TTy v1 r1 v2 r2 bt ->
       TTy v1 r1 v1 r2 (be && bt)

  TC : TTy p1 r1 v2 r2 False ->
       TTy v2 r2 v3 r3 b2    ->
       TTy p1 r1 v3 r3 b2

n : Nat -> Nat
n = (+ 2)

showInd : (indent : Nat) -> TTy p1 r1 v3 r3 br -> String
showInd i (TA x1 x2 x3) = if False
                            then (if False then show' i else show' i)
                            else showInd (n i) x1 ++ show' (n i)
                            where
                              show' : Nat -> String
                              show' i = showInd (n i) x3 ++ if False then "" else showInd (n i) x2
showInd i (TB x) = showInd (n i) x ++ if False then "" else showInd (n i) x
showInd i (TC x y) = if False then showInd i y else showInd i x ++ showInd i y

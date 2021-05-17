module Syntax

%default total

showMaybe : {0 a : Type} -> (assumption : Show a) => Maybe a -> String
showMaybe x@ma = case map (id . id) ma of
    Nothing => "Nothing"
    Just a => "Just " ++ show a

nats : List Nat
nats =
  let n = 5
      m = 7
      xs = [id $ id 0]
      ys = [1, 2, m, n, 3] ++ xs
  in [n,id $ id m] ++ [1, 2, m, n, 3] ++ xs


record ANat where
  constructor MkANat
  aNat : Nat

doBlock : Maybe ANat
doBlock
  = do let a = 3
       let b = 5
       (c, _) <- Just (7, 9)
       let (d, e) = (c, c)
       f <- [| Nothing + Just d |]
       pure $ MkANat $ sum [a,b,c,d,e,f]

parameters (x, y, z : Nat)

  add3 : Nat
  add3 = x + y + z

parameters (x, y : Nat) (z, a : Nat)

  add4 : Nat
  add4 = x + y + z + a

anonLam : Maybe (m : Nat ** n ** m === n)
anonLam = map (\m => (m ** m ** Refl))
        $ map (uncurry $ \ m, n => m + n)
        $ map (\ (m, n) => (n, m))
        $ map (\ m => (m, m))
        $ map (\ m => S m.aNat)
        doBlock

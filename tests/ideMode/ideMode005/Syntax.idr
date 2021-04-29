%default total

{- -- interfaces don't work yet
{0 a : Type} -> (foo : Show a) => Show (Maybe a) where
-}

showMaybe : {0 a : Type} -> (assumption : Show a) => Maybe a -> String
showMaybe ma = case ma of
    Nothing => "Nothing"
    Just a => "Just " ++ show a

doBlock : Maybe Nat
doBlock
  = do let a = 3
       let b = 5
       c <- Just 7
       let (d, e) = (c, c)
       f <- [| Nothing + Just d |]
       pure $ sum [a,b,c,d,e,f]

anonLam : Maybe Nat
anonLam = map (uncurry $ \ m, n => m + n)
        $ map (\ (m, n) => (n, m))
        $ map (\ m => (m, m))
        $ map (\ m => S m)
        doBlock

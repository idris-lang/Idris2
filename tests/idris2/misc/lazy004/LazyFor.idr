import Data.List.Lazy

import Debug.Trace

%default total

xs : LazyList Nat
xs = iterateN 5 (traceValBy (("xs: " ++) . show) . S) Z

ys : Maybe (List Nat)
ys = for xs $ \n => if n >= 3 then Nothing else Just (10 * n)

xs' : LazyList Nat
xs' = iterateN 5 (traceValBy (("xs': " ++) . show) . S) Z

for' : Monad f => LazyList a -> (a -> f b) -> f $ List b
for' [] _ = pure []
for' (x::xs) g = pure $ !(g x) :: !(for' xs g)

ys' : Maybe (List Nat)
ys' = for' xs' $ \n => if n >= 3 then Nothing else Just (10 * n)

main : IO ()
main = do
  putStrLn $ show ys
  putStrLn $ show ys'

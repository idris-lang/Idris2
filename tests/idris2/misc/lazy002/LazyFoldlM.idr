module LazyFoldlM

import Data.List.Lazy

import Debug.Trace

foldlM' : Monad m => (fm : b -> a -> m b) -> (init : b) -> LazyList a -> m b
foldlM' fm init xs = foldrLazy (\x, k, z => fm z x >>= k) pure xs init

l : LazyList Nat
l = (\n => trace "gen \{show n}" n) <$> iterateN 10000 (+1) 0

-- Both should be actually short-cutting (i.e., not many `gen *` should be printed)

x : Maybe Nat
x = foldlM' (\m, n => if m <= 1 then Just n else Nothing) 0 l

y : Maybe Nat
y = foldlM (\m, n => if m <= 1 then Just n else Nothing) 0 l

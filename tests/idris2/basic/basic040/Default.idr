module Default

happyPairs : List (Nat, Char)
happyPairs = map (uncurry $ \ c, n => (n, c)) [('a', 1)]

-- In Idris1 `sadPairs` is rejected with the following error:
--    |
-- 10 | sadPairs = map (\ (c, n) => (n, c)) [('a', 1)]
--    |                             ~~
-- When checking right hand side of Default.case block in sadPairs at Default.idr:10:19-24 with expected type
--         (Nat, Char)

-- When checking argument a to constructor Builtins.MkPair:
--         Type mismatch between
--                 Integer (Type of n)
--         and
--                 Nat (Expected type)


sadPairs : List (Nat, Char)
sadPairs = map (\ (c, n) => (n, c)) [('a', 1)]

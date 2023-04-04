import Data.List.Lazy

import Debug.Trace

showHead : Show a => LazyList a -> String
showHead [] = "Empty"
showHead (x::xs) = show x

%inline
(::) : Maybe a -> Lazy (LazyList a) -> LazyList a
Nothing :: xs = xs
Just x  :: xs = x :: xs

bot : a
bot = bot

fufu : a -> Maybe a
fufu = Just

g : LazyList Nat
g = [ fufu 6
    , fufu bot
    ]

-- Note that this should finish in finite time, as tail containing
-- `bot` is lazy and should never be computed
main : IO Unit
main = printLn $ showHead g

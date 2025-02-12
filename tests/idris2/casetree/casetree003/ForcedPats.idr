data View : List a -> Type where
  -- Include non-erased unit to inhibit identity optimisation
  Nil : {auto _ : ()} -> View []
  (::) : (x : a) -> (xs : List a) -> View (x :: xs)

view : (xs : List a) -> View xs
view [] = []
view (x :: xs) = x :: xs

idL : (xs : List a) -> View xs -> List a
idL .([]) [] = []
idL .(x :: xs) (x :: xs) = x :: idL xs (view xs)

{- Old compile time tree:

Compile time tree: case {arg:1} of
  Nil {e:0} => case {arg:2} of
    Nil {e:4} {e:5} => []
  (::) {e:1} {e:2} {e:3} => case {arg:2} of
    (::) {e:5} {e:6} {e:7} => {e:2} :: idL {e:3} (view {e:3})

-}

{- With dotted expressions change:

Compile time tree: case {arg:2} of
  Nil {e:0} {e:1} => []
  (::) {e:1} {e:2} {e:3} => {e:2} :: idL {e:3} (view {e:3})

-}

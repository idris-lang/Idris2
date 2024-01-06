
infix 5 -:-

(-:-) : a -> List a -> List a
(-:-) = (::)

test : List Nat
test = 4 -:- 3 -:- []


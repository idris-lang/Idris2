
private infix 5 -:-

private infix 5 :-:

(-:-) : a -> List a -> List a
(-:-) = (::)

(:-:) : a -> List a -> List a
(:-:) = (::)

test : List Nat
test = 4 -:- 3 :-: []

test2 : List Nat
test2 = 4 :-: 3 -:- []

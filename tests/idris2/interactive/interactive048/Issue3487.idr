one : {a, b : Nat} -> () -> ()
one {a, b} c = ?rhs

two : {a : Nat} ->  {b : (Nat, Nat)} -> () -> ()
two {a=x, b = (c, d)} e = ?rhs2

three : {a : Maybe Nat} -> {b : Nat} -> () -> ()
three {a = Nothing, b} c = ?rhs3
three {a = Just x} c = ?rhs4

four : { a : List Nat} -> () -> ()
four {a = [x,y]} c = ?rhs5
four {a = xs} c = ?rhs6

five : Nat -> Nat
five x = (case x of
  y => ?rhs7 ) -- something y

six : Nat -> {a : Nat} -> {b, c : Nat} -> ()
six x {- is x -} {a {- is a -} } { {- here is b -} b, {- and c -} c} = ?rhs8 -- it is a x

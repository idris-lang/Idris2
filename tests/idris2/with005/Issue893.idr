module Issue893

%default total

foo : (a, b : Nat) -> Bool
foo  Z    b = False
foo (S _) b = False

notFoo : (a, b : Nat) -> Not (foo a b = True)
notFoo  Z    _ = uninhabited
notFoo (S _) _ = uninhabited

bar : (a, b : Nat) -> (foo a b) && c = foo a b
bar a b with (foo a b) proof ab
  bar a b | True  = absurd $ notFoo a b ab
  bar a b | False = Refl

goo : (a, b : Nat) -> Bool -> Bool
goo a b True = True
goo a b False = foo a b || foo a b

bar2 : (a, b : Nat) -> goo a b (foo a b) = foo a b
bar2 a b with (foo a b) proof ab
  bar2 a b | True = Refl
  bar2 a b | False = rewrite ab in Refl

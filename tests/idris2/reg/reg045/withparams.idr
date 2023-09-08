-- Testing that 'with' works under parameters that are implicits
parameters {0 A : Type} (pred : A -> Bool)
  foo : A -> Bool
  foo x = case pred x of
    True  => False
    False => True

  bar : (x : A) -> not (pred x) = foo x
  bar  a with (pred a)
   bar a | True  = Refl
   bar a | False = Refl

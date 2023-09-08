-- insert Delay
f1 : Lazy (Unit -> Unit)
f1 = \x => x

f2 : Lazy (Unit -> Unit)
f2 = Delay (\x => x)

-- can't define lazy functions by pattern matching
failing "Defining lazy functions via pattern matching is not yet supported."
  f3 : Unit -> Lazy (Unit -> Unit)
  f3 x y = y

failing "Defining lazy functions via pattern matching is not yet supported."
  f4 : Lazy (Unit -> Unit)
  f4 x = x

-- first argument has to be explicit
failing "Implicit lazy functions are not yet supported."
  f5 : Lazy ({u : Unit} -> Unit)
  f5 = Delay ()

f6 : Lazy ((u1 : Unit) -> {u2 : Unit} -> Unit)
f6 = Delay (\u1 => u1)

-- still works: delayed arguments
f7 : Unit -> Lazy (Unit -> Unit) -> Unit
f7 u g = g u

-- still works: forced forced arguments
f8 : (f : Lazy (Unit -> Unit)) -> (g : Unit -> Unit) -> f === g -> Unit
f8 .(g) g Refl = g ()

f9 : (f : Lazy (Unit -> Unit)) -> (g : Unit -> Unit) -> f === g -> Unit
f9 f .(f) Refl = f ()

f10 : (f : Lazy (Unit -> Unit)) -> (g : Unit -> Unit) -> f === g -> Unit
f10 f .(Force f) Refl = f ()

-- work-around for issue 2936
switch : Bool -> Lazy (Nat -> Nat)
switch True  = \k => k
switch False = \k => 0

switch3 : Bool -> (Nat, Nat, Nat) -> (Nat, Nat, Nat)
switch3 b = let f = switch b
        in \(x,y,z) => (f x, f y, f z)

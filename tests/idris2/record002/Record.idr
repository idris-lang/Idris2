data Vect : Nat -> Type -> Type where
     Nil : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

record MyDPair a p where
  constructor MkMyDPair
  dfst : a
  dsnd : p dfst

cons : t -> MyDPair Nat (\n => Vect n t) -> MyDPair Nat (\n => Vect n t)
cons val xs
    = record { dfst = S (dfst xs),
               dsnd = val :: dsnd xs } xs

cons' : t -> MyDPair Nat (\n => Vect n t) -> MyDPair Nat (\n => Vect n t)
cons' val
    = record { dfst $= S,
               dsnd $= (val ::) }

record Stats where
  constructor MkStats
  height : Int
  weight : Int

record Person where
  constructor MkPerson
  name : String
  age, shoesize : Int
  more : Stats

testPair : MyDPair Nat (\n => Vect n Int)
testPair = MkMyDPair _ [1,2,3,4,5]

testPerson : Person
testPerson = MkPerson "Fred" 1337 10 (MkStats 10 10)

grow : Person -> Person
grow = record { more.height $= (+1) }

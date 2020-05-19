data Vect : Nat -> Type -> Type where
     Nil : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

record MyDPair a (p : a -> Type) where
  constructor MkMyDPair
  dfst : a
  dsnd : p dfst

record DVect a where
  constructor MkDVect
  test : Int
  {n : Nat}
  vec : Vect n a

record Person where
  constructor MkPerson
  name : String
  age, shoesize : Int
  some_fn : b -> b -- 'b' bound as an argument to MkPerson

testPair : MyDPair Nat (\n => Vect n Int)
testPair = MkMyDPair _ [1,2,3,4,5]

testDVect : DVect Int
testDVect = MkDVect 94 [1,2,3,4,5]

testPerson : Person
testPerson = MkPerson "Wowbagger" 1337 10 (\x => S x)


parameters {n : Nat}
           (a : Int)
  0 func : Bool -> Type
  func True = List Bool
  func False = List Nat

  getType : (b : Bool) -> func b
  getType False = [0,1,2]
  getType True = [True, True, True]

  prf : (b : Bool) -> Int -> func b
  prf b i = let i1 = getType b in ?whut



module BhaktiTest

import Language.Reflection

%language ElabReflection 

%logging 1

data TestData : (t : Type) -> (i : Nat) -> Type where 
    C1 : (a : t) -> (ma : Maybe t) -> TestData t 0
    C2 : (x : u) -> (n : Nat) -> TestData u n
    C3 : (a : t) -> (lma : List (Maybe t)) -> TestData t 1


data Test2 : (t : Type) -> (a : t) -> Type where 
    C1 : (t : Type) -> (a : )
m = %runElab getDecEqConPairs TestData
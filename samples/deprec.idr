import Data.Vect

record Person where
    constructor MkPerson
    firstName, middleName, lastName : String
    age : Int

record SizedClass (size : Nat) where
    constructor SizedClassInfo
    students : Vect size Person
    className : String

record Class where
    constructor ClassInfo
    students : Vect n Person
    className : String

addStudent : Person -> Class -> Class
addStudent p c = record { students = p :: students c } c

addStudent' : Person -> SizedClass n -> SizedClass (S n)
addStudent' p c =  SizedClassInfo (p :: students c) (className c)

addStudent'' : Person -> SizedClass n -> SizedClass (S n)
addStudent'' p c = record { students = p :: students c } c

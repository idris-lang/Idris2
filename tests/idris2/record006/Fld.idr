module Fld

namespace SuperDog
   public export
   record SuperDog where
      constructor MkDog
      supername : String
      age : Int
      weight : Int

namespace OrdinaryDog
   public export
   record OrdinaryDog where
      constructor MkDog
      name : String
      age : Int
      weight : Int

record Other a where
   constructor MkOther
   {imp : String}
   fieldA : a
   fieldB : b


myDog_notWorking : record MkDog {name = "Sam"} -- Not all fields are covered

myDog_notWorking2 : record MkDog 
                     { age = 4
                     , age = 2
                     , weight = 12
                     , name = "Sam" } -- Duplicate names
 
myDog : ?
myDog = record MkDog { age = 4
                     , weight = 12
                     , name = "Sam" } --Disambiguation by unique fields

mySuperDog : ?
mySuperDog = record MkDog { age = 3
                          , weight = 10
                          , supername = "Super-Sam" } --Disambiguation by unique fields

other : ? -- Elaborates as (MkOther (fromString "hi") (the Int 1) {imp = fromString "Secret string"})
other = record MkOther {fieldB = the Int 1, fieldA = "hi"} {imp = "Secret string"}

same : record MkDog {name = "Rex", age = 2, weight = 10} = MkDog "Rex" 2 10
same = Refl

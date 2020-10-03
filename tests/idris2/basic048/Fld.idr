
import Data.Maybe
import Data.Nat

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

myDog : OrdinaryDog
myDog = MkDog { age = 4
              , weight = 12
              , name = "Sam" }

mySuperDog : SuperDog
mySuperDog = MkDog { age = 3
                   , weight = 10
                   , supername = "Super-Sam" }

other : ?
other = MkOther {fieldB = the Int 1, fieldA = "hi", imp = "Secret string"}

otherOk1 : Main.other.fieldB = (the Int 1)
otherOk1 = Refl

otherOk2 : Main.other.fieldA = "hi"
otherOk2 = Refl

otherOk3 : Main.other.imp = "Secret string"
otherOk3 = Refl

same : MkDog {age = 2, name = "Rex", weight = 10} = (the OrdinaryDog $ MkDog "Rex" 2 10)
same = Refl

namespace R1

  public export
  record R1 where
    constructor MkR
    field : a

namespace R2

  public export
  record R2 where
    constructor MkR
    {auto field : a}

r1 : R1
r1 = MkR {field = "string"}

r2_shouldNotTypecheck1 : ?
r2_shouldNotTypecheck1 = MkR {field = the Nat 22} -- fail, impossible to disambiguate

onlyName : OrdinaryDog -> String
onlyName (MkDog {name, _}) = name

mapName : (String -> String) -> OrdinaryDog -> OrdinaryDog
mapName f = {name $= f}

setName : String -> OrdinaryDog -> OrdinaryDog
setName name' = {name := name'}

setNameOld : String -> OrdinaryDog -> OrdinaryDog
setNameOld name' = record {name = name'}

interface Show a => (num : Num a) => MyIface a where -- Some interface with
   constructor MkIface
                                             -- constraints
   data MyData : a -> Type                   -- and a data declaration.
   someFunc : a -> a                         -- Constraints are now elaborated as auto implicits (as one would expect)
   giveBack : {x : a} -> MyData x -> a       -- (previously as explicit arguments of the interface
                                             -- constructor)


data MyDataImpl : a -> Type where            -- implementation of MyData
     MkMyData : (x : a) -> MyDataImpl x

-- implementation MyIface Int where
--    MyData = MyDataImpl
--    someFunc = id
--    giveBack (MkMyData x) = x

%hint
instanceMyIfaceInt : MyIface Integer -- this def, roughly speaking, is the 'same thing' as the above implementation
                                     -- Show Int, Num Int are auto implicits vvv
instanceMyIfaceInt = MkIface { MyData = MyDataImpl
                             , someFunc = id
                             , giveBack = \(MkMyData x) => x
                             , num = %search } -- auto implicit names are preserved

instanceOk : giveBack (MkMyData 22) = 22
instanceOk = Refl

interface Show' a where -- can be used in types
   constructor MkShow'
   show' : a -> String


Show' String where
   show' = id

%hint
showMaybe' : Show' a => Show' (Maybe a)
showMaybe' = MkShow' { show' = fromMaybe "Nothing" . (("Just " ++ ) . show' <$>) }

showMaybe'Ok : show' (Just "nice") = "Just nice"
showMaybe'Ok = Refl

record AllFieldTypes a where
   constructor MkAllFieldTypes
   exp : a
   {imp : a}
   {auto aut : a}

testAllFieldTypesOk : MkAllFieldTypes { aut = "aut"
                                      , exp = "exp"
                                      , imp = "imp" }
                      = MkAllFieldTypes "exp" {imp = "imp"} @{"aut"}
testAllFieldTypesOk = Refl

test4 : {auto a : String} -> {auto a : String} -> String
test4 @{a} @{a'} = show' a ++ ":" ++ show' a'

-- unnamed explicit takes priority
test5 : (a : String) -> (a : String) -> String
test5 {a = a2} {-snd-} a1 {-fst-} = a1 ++ a2

test5Ok : Main.test5 "abc" "def" = "abcdef"
test5Ok = Refl

-- unnamed auto takes priority
testAutoPriorityOk : Main.test4 {a = "2"} @{"1"} = "1:2"
testAutoPriorityOk = Refl

sameNamesOk : (a : String) -> (a : Nat) -> (String, Nat)
sameNamesOk {a, a = b} = (a, b)

eachArgType : (a : String) -> {a : String} -> {auto a : String} -> String
eachArgType {a = a1, a = a2, a = a3} = a1 ++ a2 ++ a3

eachArgTypeOk : eachArgType @{"3"} "1" {a = "2"} = "123"
eachArgTypeOk = Refl

eachArgTypeOk2 : eachArgType {a = "1", a = "2", a = "3"} = "123"
eachArgTypeOk2 = Refl

dontCare : (x : String) -> (y : String) -> (z : String) -> String
dontCare {x, z, _} = x ++ z

dontCareOk : Main.dontCare "a" "b" "c" = "ac"
dontCareOk = Refl

dontCare2 : (x : Nat) -> Nat -> Nat -> Nat -> (y : Nat) -> x + y = y + x
dontCare2 {} = plusCommutative {}
-- dontCare2 _ _ _ _ _ = plusCommutative _ _

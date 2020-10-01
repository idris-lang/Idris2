
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
other = MkOther {fieldB = the Int 1, fieldA = "hi"} {imp = "Secret string"}

same : MkDog {name = "Rex", age = 2, weight = 10} = (the OrdinaryDog $ MkDog "Rex" 2 10)
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

r2_shouldNotTypecheck3 : ?
r2_shouldNotTypecheck3 = MkR {field = the Nat 22} -- fail, impossible to disambiguate

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

test0 : (x : Nat) -> Nat -> Nat -> Nat -> (y : Nat) -> x + y = y + x
test0 {} = plusCommutative {}
-- test0 _ _ _ _ _ = plusCommutative _ _

onlyName : OrdinaryDog -> String
onlyName (MkDog {name, _}) = name

mapName : (String -> String) -> OrdinaryDog -> OrdinaryDog
mapName f = {name $= f}

setName : String -> OrdinaryDog -> OrdinaryDog
setName name' = {name := name'}

setNameOld : String -> OrdinaryDog -> OrdinaryDog
setNameOld name' = record {name = name'}

%hint
instanceMyIfaceInt : MyIface Integer -- this def, roughly speaking, is the 'same thing' as the above implementation
                                     -- Show Int, Num Int are auto implicits vvv
instanceMyIfaceInt = MkIface { MyData = MyDataImpl
                             , someFunc = id
                             , giveBack = \(MkMyData x) => x} {num = %search} -- auto implicit names are preserved

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

record Auto a where
   constructor MkAuto
   {auto aut : a}

testAuto : Auto String
testAuto = MkAuto @{"works"}

record Implicit a where
   constructor MkImplicit
   {imp : a}

testImplicit : Implicit String
testImplicit = MkImplicit {imp = "NotOk"}

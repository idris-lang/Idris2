
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

------ Using new application syntax as sugar for data instantiation (be it data/record/interface) -------

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
    -- `a` is out of scope here so
    -- this silently declares an implicit field `0 a : Type`
    field : a

namespace R2

  public export
  record R2 where
    constructor MkR
    {auto field : a}

r1 : R1 -- explicit fields access
r1 = MkR {field = "string"}

r2_shouldNotTypecheck1 : ?
r2_shouldNotTypecheck1 = MkR {field = the Nat 22} -- fail, impossible to disambiguate

interface Show a => (num : Num a) => MyIface a where -- Some interface with
  constructor MkIface
                                             -- constraints
  data MyData : a -> Type                    -- and a data declaration.
  someFunc : a -> a                          -- Constraints are now elaborated as auto implicits (as one would expect)
  giveBack : {x : a} -> MyData x -> a        -- (previously as explicit arguments of the interface
                                             -- constructor)


data MyDataImpl : a -> Type where            -- implementation of MyData
  MkMyData : (x : a) -> MyDataImpl x

-- implementation MyIface Int where
--    MyData = MyDataImpl
--    someFunc = id
--    giveBack (MkMyData x) = x

%hint
instanceMyIfaceInt : MyIface Integer -- this def, roughly speaking, is the 'same thing' as the above implementation
                                     -- Show Int, Num Int are auto implicits of MkIface
instanceMyIfaceInt = MkIface { MyData = MyDataImpl
                             , someFunc = id
                             , giveBack = \(MkMyData x) => x
                             , num = %search } -- auto implicit names are preserved

instanceOk : giveBack (MkMyData 22) = 22
instanceOk = Refl

interface Show' a where -- unlike Show, Show' reduces in types
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

-------------------------------------

------  The Update syntax --------

mapName : (String -> String) -> OrdinaryDog -> OrdinaryDog
mapName f = {name $= f}

setName : String -> OrdinaryDog -> OrdinaryDog
setName name' = {name := name'}

data Three : Type -> Type -> Type -> Type where
  MkThree : (x : a) -> (y : b) -> (z : c) -> Three a b c

mapSetMap : (a -> a') -> b' -> (c -> c') -> Three a b c -> Three a' b' c'
mapSetMap f y' g = {x $= f, y := y', z $= g}

setNameOld : String -> OrdinaryDog -> OrdinaryDog
setNameOld name' = {name := name'}

-------------------------------------

--------- Applications in presence of duplicate names ----------

-- Duplicate names are ok and treated sequentially
testDuplicateNames : {auto a : String} -> {auto a : String} -> String
testDuplicateNames @{a} @{a'} = show' a ++ ":" ++ show' a'

-- When binding arguments on LHS or listing arguments to
-- a function on RHS
-- unnamed arguments always take priority over named,
-- i.e they are bound/applied first,
-- regardless of their relative positions to named ones
testOrder1 : (a : String) -> (a : String) -> String
testOrder1 {a = a2} {-snd-} a1 {-fst-} = a1 ++ a2

testOrder1Ok : Main.testOrder1 "abc" "def" = "abcdef"
testOrder1Ok = Refl

-- unnamed explicit "1" is passed first, followed by named {a = "2"}
testAutoPriorityOk : Main.testOrder1 {a = "2"} "1" = "12"
testAutoPriorityOk = Refl

-- Two arguments with the same name can be successfully bound
-- if one of them is renamed in patterns.
-- As both arguments are requested by name
-- They are bound in the same order they are given
sameNamesOk : (a : String) -> (a : Nat) -> (String, Nat)
sameNamesOk {a {- = a-}, a = b} = (a, b)

-- All arguments are named and are of different `plicities`. Binds occur sequentially.
-- Arguments are renamed on LHS
eachArgType : (a : String) -> {a : String} -> {auto a : String} -> String
eachArgType {a = a1, a = a2, a = a3} = a1 ++ a2 ++ a3

eachArgTypeOk : eachArgType @{"3"} "1" {a = "2"} = "123"
eachArgTypeOk = Refl

-- Arguments with the same names are provided on RHS
-- which is ok, they are passed sequentially.
eachArgTypeOk2 : eachArgType {a = "1", a = "2", a = "3"} = "123"
eachArgTypeOk2 = Refl

----------------------------------------

--------- Bind-all-explicits pattern ----------

-- This pattern works like inexhaustible supply of
-- `_` (Match-any patterns).

-- Here to complete the definition we only
-- need to know the name of the OrdinaryDog.
-- We bind it with `{name, _}` also stating that
-- any extra explicits should be disregarded,
-- by inserting `_` into the braces.
onlyName : OrdinaryDog -> String
onlyName (MkDog {name, _ {-age, weight-} }) = name

dontCare : (x : String) -> (y : String) -> (z : String) -> String
dontCare {x, z, _} = x ++ z

dontCareOk : Main.dontCare "a" "b" "c" = "ac"
dontCareOk = Refl

-- If none of the explicit arguments are wanted
-- one `{}` can be used instead of writing an underscore for each.
dontCare2 : (x : Nat) -> Nat -> Nat -> Nat -> (y : Nat) -> x + y = y + x
dontCare2 {} = plusCommutative {}
-- dontCare2 _ _ _ _ _ = plusCommutative _ _

data Tree a = Leaf a | Node (Tree a) a (Tree a)

isNode : Tree a -> Bool
isNode (Node {}) = True
isNode _ = False

data IsNode : Tree a -> Type where
  Is : IsNode (Node {})

decIsNode : (x : Tree a) -> Dec (IsNode x)
decIsNode (Node {}) = Yes Is
decIsNode (Leaf {}) = No (\case Is impossible)
------------------------------------------------

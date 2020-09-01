module Fld

import Data.Maybe

-- For now I kept this syntax:
-- record < (data) Constructor or _ > { <field1> = <expr1>, <field2> = <expr2>, ..., <fieldN> = <exprN> }
-- What would be a reason to have named constructors anyway, if we were to instantiate records by their
                                                                        -- type constructors ?

-- Also it turned out that specifying type constructors instead of data constructors
--      does not simplify or provide any other benifit in internal implementation.


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

myDog_shouldNotTypecheck0 : record MkDog {name = "Sam"}           -- Not all fields are covered

myDog_shouldNotTypecheck1 : record MkDog {age = 3, name1 = "Sam"} -- No constructor with name `MkDog`
                                                                  -- has field `name1`
myDog_shouldNotTypecheck2 : record MkDog
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

record Unit where
  constructor MkUnit

unit : Fld.Unit
unit = record _ {} -- infer the constructor

namespace R1

  public export
  record R1 where
    constructor MkR
    field : a

namespace R2

  public export
  record R2 where
    constructor MkR
    field : a

r1 : R1
r1 = record _ {field = "string"} -- type-driven disambiguation

r2_shouldNotTypecheck3 : ?
r2_shouldNotTypecheck3 = record MkR {field = the Nat 22} -- fail, impossible to disambiguate

r3_shouldNotTypecheck4 : ?
r3_shouldNotTypecheck4 = record _ {field = the Nat 22} -- fail, impossible to disambiguate

r4 : ?
r4 = the R2 $ record _ {field = the Nat 22} -- ok

sillyShow : String -> String -- shows string as is, constructs an instance of Show String
sillyShow str = show @{ record _ {show = id, showPrec = const id} } str -- TODO default implementations not yet supported

sillyShowOk : sillyShow "x" = "x"
sillyShowOk = Refl

interface Show a => (num : Num a) => MyIface a where -- Some interface with
   --constructor MkMyIface, not needed :)    -- constraints
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
instanceMyIfaceInt = record _ {MyData = MyDataImpl, someFunc = id, giveBack = \(MkMyData x) => x} {num = %search} -- auto implicit names are preserved

instanceOk : giveBack (MkMyData 22) = 22
instanceOk = Refl

interface Show' a where -- can be used in types
   show' : a -> String


Show' String where
   show' = id

%hint
showMaybe' : Show' a => Show' (Maybe a)
showMaybe' = record _ { show' = fromMaybe "Nothing" . (("Just " ++ ) . show' <$>) }

showMaybe'Ok : show' (Just "nice") = "Just nice"
showMaybe'Ok = Refl

record Auto a where
   {auto aut : a}

testAuto : Auto String
testAuto = record _ {} @{"works"}

record Implicit a where
   {imp : a}

testImplicit : Implicit String
testImplicit = record _ {imp = "NotOk"} --TODO imp is an implicit argument
                                        -- why suddenly does it become explicit ?
                                        -- This is current idris behaviour
                                        -- FIX IT !


-- What about different syntax for this: "new {...}   = record _ {...}"
--                                       "new _ {...} = record _ {...}"
--                                       "new x {...} = record x {...}" ?

-- Saves a little bit of typing and allows omitting the "_" .
-- Also "new" is quite frequently used in programming languages
--      with the meaning "make an instance of something"

-- We can't have "record {...} = record _ {...}" as it intersects with record update syntax

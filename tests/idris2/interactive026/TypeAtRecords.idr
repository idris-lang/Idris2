||| Test if :typeat can report the type of variables in record definitions
||| and record updates

-- `pet` is an excuse to have a type variable
record Person animal where
  name : String
  age : Nat
  pet : animal

-- Record update syntax with the record keyword

singleFieldUpdate : Person a -> Person a
singleFieldUpdate p = { age $= (+one) } p
-- Not making it point free to keep a var here ^
  where
    -- A variable to use in the update
    one : Nat
    one = 1

multiFieldUpdate : Person a -> Person a
multiFieldUpdate p = { name := emptyString, age := zero } p
-- Not point free just like above, in order to have a var here ^
  where
    -- Variables to use in the update
    emptyString : String
    emptyString = ""

    zero : Nat
    zero = 0

-- :typeat in a record update using the syntax without the `record` keyword
-- doesn't yet work

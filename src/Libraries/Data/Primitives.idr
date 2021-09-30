||| TODO : This was interduced after v0.5.1. After the next minor release,
|||        this can be removed and the instances from `base` can be used.
module Libraries.Data.Primitives

import public Decidable.Equality.Core as Decidable.Equality

%default total

--------------------------------------------------------------------------------
-- Bits8
--------------------------------------------------------------------------------

public export
[TempB8] DecEq Bits8 where
    decEq x y = case x == y of -- Blocks if x or y not concrete
                     True => Yes primitiveEq
                     False => No primitiveNotEq
       where primitiveEq : forall x, y . x = y
             primitiveEq = believe_me (Refl {x})
             primitiveNotEq : forall x, y . Not (x = y)
             primitiveNotEq prf = believe_me {b = Void} ()

--------------------------------------------------------------------------------
-- Bits16
--------------------------------------------------------------------------------

public export
[TempB16] DecEq Bits16 where
    decEq x y = case x == y of -- Blocks if x or y not concrete
                     True => Yes primitiveEq
                     False => No primitiveNotEq
       where primitiveEq : forall x, y . x = y
             primitiveEq = believe_me (Refl {x})
             primitiveNotEq : forall x, y . Not (x = y)
             primitiveNotEq prf = believe_me {b = Void} ()

--------------------------------------------------------------------------------
-- Bits32
--------------------------------------------------------------------------------

public export
[TempB32] DecEq Bits32 where
    decEq x y = case x == y of -- Blocks if x or y not concrete
                     True => Yes primitiveEq
                     False => No primitiveNotEq
       where primitiveEq : forall x, y . x = y
             primitiveEq = believe_me (Refl {x})
             primitiveNotEq : forall x, y . Not (x = y)
             primitiveNotEq prf = believe_me {b = Void} ()

--------------------------------------------------------------------------------
-- Bits64
--------------------------------------------------------------------------------

public export
[TempB64] DecEq Bits64 where
    decEq x y = case x == y of -- Blocks if x or y not concrete
                     True => Yes primitiveEq
                     False => No primitiveNotEq
       where primitiveEq : forall x, y . x = y
             primitiveEq = believe_me (Refl {x})
             primitiveNotEq : forall x, y . Not (x = y)
             primitiveNotEq prf = believe_me {b = Void} ()

--------------------------------------------------------------------------------
-- Int8
--------------------------------------------------------------------------------

public export
[TempI8] DecEq Int8 where
    decEq x y = case x == y of -- Blocks if x or y not concrete
                     True => Yes primitiveEq
                     False => No primitiveNotEq
       where primitiveEq : forall x, y . x = y
             primitiveEq = believe_me (Refl {x})
             primitiveNotEq : forall x, y . Not (x = y)
             primitiveNotEq prf = believe_me {b = Void} ()

--------------------------------------------------------------------------------
-- Int16
--------------------------------------------------------------------------------

public export
[TempI16] DecEq Int16 where
    decEq x y = case x == y of -- Blocks if x or y not concrete
                     True => Yes primitiveEq
                     False => No primitiveNotEq
       where primitiveEq : forall x, y . x = y
             primitiveEq = believe_me (Refl {x})
             primitiveNotEq : forall x, y . Not (x = y)
             primitiveNotEq prf = believe_me {b = Void} ()

--------------------------------------------------------------------------------
-- Int32
--------------------------------------------------------------------------------

public export
[TempI32] DecEq Int32 where
    decEq x y = case x == y of -- Blocks if x or y not concrete
                     True => Yes primitiveEq
                     False => No primitiveNotEq
       where primitiveEq : forall x, y . x = y
             primitiveEq = believe_me (Refl {x})
             primitiveNotEq : forall x, y . Not (x = y)
             primitiveNotEq prf = believe_me {b = Void} ()

--------------------------------------------------------------------------------
-- Int64
--------------------------------------------------------------------------------

public export
[TempI64] DecEq Int64 where
    decEq x y = case x == y of -- Blocks if x or y not concrete
                     True => Yes primitiveEq
                     False => No primitiveNotEq
       where primitiveEq : forall x, y . x = y
             primitiveEq = believe_me (Refl {x})
             primitiveNotEq : forall x, y . Not (x = y)
             primitiveNotEq prf = believe_me {b = Void} ()

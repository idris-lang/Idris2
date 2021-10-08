||| TODO : This was interduced after v0.5.1. After the next minor release,
|||        this can be removed and the instances from `base` can be used.
module Libraries.Data.Primitives

import public Decidable.Equality.Core as Decidable.Equality

%default total

public export
[FromEq] Eq a => DecEq a where
    decEq x y = case x == y of -- Blocks if x or y not concrete
                     True => Yes primitiveEq
                     False => No primitiveNotEq
       where primitiveEq : forall x, y . x = y
             primitiveEq = believe_me (Refl {x})
             primitiveNotEq : forall x, y . Not (x = y)
             primitiveNotEq prf = believe_me {b = Void} ()

--------------------------------------------------------------------------------
-- Bits8
--------------------------------------------------------------------------------

public export
[TempB8] DecEq Bits8 where
    decEq = decEq @{FromEq}

--------------------------------------------------------------------------------
-- Bits16
--------------------------------------------------------------------------------

public export
[TempB16] DecEq Bits16 where
    decEq = decEq @{FromEq}

--------------------------------------------------------------------------------
-- Bits32
--------------------------------------------------------------------------------

public export
[TempB32] DecEq Bits32 where
    decEq = decEq @{FromEq}

--------------------------------------------------------------------------------
-- Bits64
--------------------------------------------------------------------------------

public export
[TempB64] DecEq Bits64 where
    decEq = decEq @{FromEq}

--------------------------------------------------------------------------------
-- Int8
--------------------------------------------------------------------------------

public export
[TempI8] DecEq Int8 where
    decEq = decEq @{FromEq}

--------------------------------------------------------------------------------
-- Int16
--------------------------------------------------------------------------------

public export
[TempI16] DecEq Int16 where
    decEq = decEq @{FromEq}

--------------------------------------------------------------------------------
-- Int32
--------------------------------------------------------------------------------

public export
[TempI32] DecEq Int32 where
    decEq = decEq @{FromEq}

--------------------------------------------------------------------------------
-- Int64
--------------------------------------------------------------------------------

public export
[TempI64] DecEq Int64 where
    decEq = decEq @{FromEq}

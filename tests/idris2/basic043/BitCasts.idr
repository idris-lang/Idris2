-- Tests to check that casting between integer types works as expected
--
-- The tests in `idris2/basic043`, `chez/chez029` and `node/node022` are the
-- same and should all have the same output.

--
-- Widening should not have any effect
--

bits8WideningNoEffect : List String
bits8WideningNoEffect = [
    show $ cast {from = Bits8} {to = Bits16} 123,
    show $ cast {from = Bits8} {to = Bits32} 123,
    show $ cast {from = Bits8} {to = Bits64} 123,
    show $ cast {from = Bits8} {to = Int} 123,
    show $ cast {from = Bits8} {to = Integer} 123
]

bits16WideningNoEffect : List String
bits16WideningNoEffect = [
    show $ cast {from = Bits16} {to = Bits32} 1234,
    show $ cast {from = Bits16} {to = Bits64} 1234,
    show $ cast {from = Bits16} {to = Int} 1234,
    show $ cast {from = Bits16} {to = Integer} 1234
]

bits32WideningNoEffect : List String
bits32WideningNoEffect = [
    show $ cast {from = Bits32} {to = Bits64} 1234567,
    show $ cast {from = Bits32} {to = Int} 1234567,
    show $ cast {from = Bits32} {to = Integer} 1234567
]

--
-- Narrowing
--

b8max : Integer
b8max = 0x100

b16max : Integer
b16max = 0x10000

b32max : Integer
b32max = 0x100000000

b64max : Integer
b64max = 18446744073709551616 -- 0x10000000000000000


narrowFromInteger : List String
narrowFromInteger = [
    show $ cast {from = Integer} {to = Bits8} (b8max + 134),
    show $ cast {from = Integer} {to = Bits16} (b16max + 134),
    show $ cast {from = Integer} {to = Bits32} (b32max + 134),
    show $ cast {from = Integer} {to = Bits64} (b64max + 134)
]

narrowFromInt : List String
narrowFromInt = [
    show $ cast {from = Int} {to = Bits8} (cast (b8max + 134)),
    show $ cast {from = Int} {to = Bits16} (cast (b16max + 134)),
    show $ cast {from = Int} {to = Bits32} (cast (b32max + 134)),
    show $ cast {from = Int} {to = Bits64} (cast (b64max + 134))
]

narrowFromBits64 : List String
narrowFromBits64 = [
    show $ cast {from = Bits64} {to = Bits8} (cast (b8max + 134)),
    show $ cast {from = Bits64} {to = Bits16} (cast (b16max + 134)),
    show $ cast {from = Bits64} {to = Bits32} (cast (b32max + 134))
]

narrowFromBits32 : List String
narrowFromBits32 = [
    show $ cast {from = Bits32} {to = Bits8} (cast (b8max + 134)),
    show $ cast {from = Bits32} {to = Bits16} (cast (b16max + 134))
]

narrowFromBits16 : List String
narrowFromBits16 = [
    show $ cast {from = Bits16} {to = Bits8} (cast (b8max + 134))
]

--
-- Negative numbers
--

negativeNumberCast : List String
negativeNumberCast = [
    show $ cast {to = Bits8} (-19),
    show $ cast {to = Bits16} (-19),
    show $ cast {to = Bits32} (-19),
    show $ cast {to = Bits64} (-19)
]

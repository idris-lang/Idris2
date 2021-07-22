module UnderscoredIntegerLiterals

-- grouping decimal numbers by thousands
amount : Integer
amount = 10_000_000_000

equalAmounts : Bool
equalAmounts = amount == 10000000000

-- grouping hexadecimal addresses by words
addr : Int
addr = 0xCAFE_F00D

equalAddrs : Bool
equalAddrs = addr == 0xCAFEF00D

-- grouping bits into nibbles in a binary literal
equalFlags : Bool
equalFlags = 0b0011_1111_0100_1110 == 0b0011111101001110

-- grouping octals
equalOctals : Bool
equalOctals = 0o455_777 == 0o455777

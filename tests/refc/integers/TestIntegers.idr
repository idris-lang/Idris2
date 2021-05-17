module TestIntegers

import Data.List.Quantifiers

put : Show a => a -> IO ()
put = putStrLn . show

castAllTo : (to : Type)
         -> {0 types : List Type}
         -> All (flip Cast to) types => HList types -> List to
castAllTo to = forget . imapProperty (flip Cast to) (cast {to})

main : IO ()
main = do
    let ints = the (HList _) [
        the Bits8 0, -- Bits8 min
        the Bits8 50,
        the Bits8 255, -- Bits8 max
        the Bits16 0, -- Bits16 min
        the Bits16 10000,
        the Bits16 65535, -- Bits16 max
        the Bits32 0, -- Bits32 min
        the Bits32 1000000000,
        the Bits32 4294967295, -- Bits32 max
        the Bits64 0, -- Bits64 min
        the Bits64 5000000000000000000,
        the Bits64 18446744073709551615, -- Bits64 max
        the Int $ -9223372036854775808, -- Int min
        the Int 1000000000000000000,
        the Int 9223372036854775807, -- Int max
        the Integer $ -9223372036854775809, -- Int min - 1
        the Integer 9223372036854775808 -- Int max + 1
    ]

    putStrLn "Cast to String:"
    put ints

    putStrLn "Cast to Bits8:"
    put $ castAllTo Bits8 ints

    putStrLn "Cast to Bits16:"
    put $ castAllTo Bits16 ints

    putStrLn "Cast to Bits32:"
    put $ castAllTo Bits32 ints

    putStrLn "Cast to Bits64:"
    put $ castAllTo Bits64 ints

    putStrLn "Cast to Int:"
    put $ castAllTo Int ints

    putStrLn "Cast to Integer:"
    put $ castAllTo Integer ints

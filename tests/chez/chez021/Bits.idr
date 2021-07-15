t1 : Bits8
t1 = 2

t2 : Bits8
t2 = 255

t3 : Bits8
t3 = 100

tests8 : List String
tests8 = map show [t1 + t2,
                   t1 * t3,
                   the Bits8 (fromInteger (-8)),
                   the Bits8 257,
                   the Bits8 (fromInteger (-1)),
                   prim__shl_Bits8 t3 1,
                   prim__shl_Bits8 t2 1]

testsCmp : List String
testsCmp = map show [t1 < t2, t3 < (t2 + t1)]

testsMax : List String
testsMax = [show (the Bits8 (fromInteger (-1))),
            show (the Bits16 (fromInteger (-1))),
            show (the Bits32 (fromInteger (-1))),
            show (the Bits64 (fromInteger (-1)))]

main : IO ()
main
    = do printLn (t1 + t2)
         printLn (t1 * t3)
         printLn (t1 < t2)
         printLn (prim__shl_Bits8 t3 1)
         printLn (prim__shl_Bits8 t2 1)
         printLn (t3 < (t2 + t1))
         printLn (the Bits8 (fromInteger (-8)))
         printLn (the Bits8 257)
         printLn (the Bits64 1234567890)
         printLn (the Bits8 (fromInteger (-1)))
         printLn (the Bits16 (fromInteger (-1)))
         printLn (the Bits32 (fromInteger (-1)))
         printLn (the Bits64 (fromInteger (-1)))

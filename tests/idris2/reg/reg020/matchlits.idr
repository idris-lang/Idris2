test1 : Int -> Int
test1 0b101 = 5
test1 0x100 = 42
test1 0o100 = 43
test1 1234567890 = 44
test1 _         = 0

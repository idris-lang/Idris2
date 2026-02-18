%default total

data MyBit = A | B

fullCoverage : MyBit -> Int
fullCoverage A = 1
fullCoverage B = 2

extraDefault : MyBit -> Int
extraDefault A = 1
extraDefault B = 2
extraDefault _ = 3

usefulDefault : MyBit -> Int
usefulDefault A = 1
usefulDefault _ = 2

earlyDefault : MyBit -> Int
earlyDefault _ = 1
earlyDefault A = 2

onlyDefault : MyBit -> Int
onlyDefault _ = 1

nestedFullCoverage : MyBit -> MyBit -> Int
nestedFullCoverage A A = 1
nestedFullCoverage A B = 2
nestedFullCoverage B A = 3
nestedFullCoverage B B = 4

nestedExtraDefault : MyBit -> MyBit -> Int
nestedExtraDefault A A = 1
nestedExtraDefault A B = 2
nestedExtraDefault B A = 3
nestedExtraDefault B B = 4
nestedExtraDefault _ _ = 5

nestedUsefulDefault : MyBit -> MyBit -> Int
nestedUsefulDefault A A = 1
nestedUsefulDefault A B = 2
nestedUsefulDefault B A = 3
nestedUsefulDefault _ _ = 4

nestedEarlyDefault : MyBit -> MyBit -> Int
nestedEarlyDefault A A = 1
nestedEarlyDefault A B = 2
nestedEarlyDefault B A = 3
nestedEarlyDefault _ _ = 4
nestedEarlyDefault B B = 5

import Data.Double

-- adding the rounding unit to a Double should not modify it

testOnePlusRU : Bool
testOnePlusRU = 1.0 + roundingUnit == 1.0

testRUPlusOne : Bool
testRUPlusOne = roundingUnit + 1.0 == 1.0

testRUComm : Bool
testRUComm = testOnePlusRU == testRUPlusOne


-- the machine epsilon should be double the rounding unit

testEps2U : Bool
testEps2U = epsilon == roundingUnit * 2.0


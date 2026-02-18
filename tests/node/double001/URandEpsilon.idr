import Data.Double

-- adding the rounding unit to a Double should not modify it

testOnePlusUR : Bool
testOnePlusUR = 1.0 + unitRoundoff == 1.0

testURPlusOne : Bool
testURPlusOne = unitRoundoff + 1.0 == 1.0

testURComm : Bool
testURComm = testOnePlusUR == testURPlusOne


-- the machine epsilon should be double the rounding unit

testEps2UR : Bool
testEps2UR = epsilon == unitRoundoff * 2.0

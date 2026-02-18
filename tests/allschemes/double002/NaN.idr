import Data.Double

-- undefined things are NaN
divZeroZero : Double
divZeroZero = 0.0 / 0.0

-- NaN with anything is NaN

nanPlus : Double
nanPlus = 1.0 + nan

nanSub : Double
nanSub = 1.0 - nan

nanMult : Double
nanMult = 2.0 * nan

nanDiv : Double
nanDiv = nan / 2.0

-- neg NaN is still NaN
negNaN : Double
negNaN = negate nan

-- NaNs are never equal
nansNotEq : Bool
nansNotEq = nan == nan

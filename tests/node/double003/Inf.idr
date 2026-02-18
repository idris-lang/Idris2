import Data.Double

-- negating positive inf (should give negative inf)
negInf : Double
negInf = negate inf

-- dividing non-zero by zero tends to infinity
divNZbyZero : Bool
divNZbyZero = 1.0 / 0.0 == inf

-- adding pos-inf to pos-inf gives pos-inf
addPosInfs : Bool
addPosInfs = inf + inf == inf

-- subbing inf from neg-inf gives neg-inf
subNegInfs : Bool
subNegInfs = -inf - inf == -inf

-- subtracting pos-inf from pos-inf is nan
-- (can't use `==` because no nans are equal)
subPosInf : Double
subPosInf = inf - inf

-- adding pos-inf to neg-inf is nan
-- (can't use `==` because no nans are equal)
addNegInf : Double
addNegInf = -inf + inf

-- neg-inf by neg-inf gives pos-inf
squareNegInfIsPosInf : Bool
squareNegInfIsPosInf = pow (-inf) 2 == inf

-- pos-inf by pos-inf gives pos-inf
squarePosInfIsPosInf : Bool
squarePosInfIsPosInf = pow inf 2 == inf

-- pos-inf by neg-inf is neg-inf
multInfSignFlip : Bool
multInfSignFlip = inf * (-inf) == -inf

-- pos-inf is equal to some other pos-inf
posInfIsPosInf : Bool
posInfIsPosInf = inf == pow inf 2

-- neg-inf is equal to some other neg-inf
negInfIsNegInf : Bool
negInfIsNegInf = -inf == pow (-inf) 3

-- pos-inf is not neg-inf
posInfEqNegInf : Bool
posInfEqNegInf = inf == -inf

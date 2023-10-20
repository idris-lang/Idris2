||| Various IEEE floating-point number constants
module Data.Double

-- TODO:
--   * update changelog

%foreign "scheme:blodwen-calcFlonumUnitRoundoff"
         "node:lambda:()=>Number.EPSILON / 2"
||| Largest number that can be added to a floating-point number without changing
||| its value, i.e. `1.0 + unitRoundoff == 1.0`.
export
unitRoundoff : Double

%foreign "scheme,chez:blodwen-calcFlonumEpsilon"
         "scheme,racket:blodwen-flonumEpsilon"
         "node:lambda:()=>Number.EPSILON"
||| Machine epsilon is the smallest floating-point number that distinguishes two
||| floating-point numbers; the step size on the floating-point number line.
export
epsilon : Double


%foreign "scheme:blodwen-flonumNaN"
         "node:lambda:()=>Number.NaN"
||| Not a number, e.g. `0.0 / 0.0`. Never equal to anything, including itself.
export
nan : Double


%foreign "scheme:blodwen-flonumInf"
         "node:lambda:()=>Infinity"
||| Positive Infinity. Can be negated to obtain Negative Infinity.
export
inf : Double


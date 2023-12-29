||| Various IEEE floating-point number constants
module Data.Double

||| Largest number that can be added to a floating-point number without changing
||| its value, i.e. `1.0 + unitRoundoff == 1.0`.
%foreign "scheme:blodwen-calcFlonumUnitRoundoff"
         "node:lambda:()=>Number.EPSILON / 2"
export
unitRoundoff : Double

||| Machine epsilon is the smallest floating-point number that distinguishes two
||| floating-point numbers; the step size on the floating-point number line.
-- /!\ See `support/racket/support.rkt:42-45`
-- %foreign "scheme,chez:blodwen-calcFlonumEpsilon"
--          "scheme,racket:blodwen-flonumEpsilon"
%foreign "scheme:blodwen-calcFlonumEpsilon"
         "node:lambda:()=>Number.EPSILON"
export
epsilon : Double


||| Not a number, e.g. `0.0 / 0.0`. Never equal to anything, including itself.
%foreign "scheme:blodwen-flonumNaN"
         "node:lambda:()=>Number.NaN"
export
nan : Double


||| Positive Infinity. Can be negated to obtain Negative Infinity.
%foreign "scheme:blodwen-flonumInf"
         "node:lambda:()=>Infinity"
export
inf : Double


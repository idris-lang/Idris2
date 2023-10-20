||| Various IEEE floating-point number constants
module Data.Double

-- TODO:
--   * docstrings
--   * update changelog

%foreign "scheme:blodwen-calcFlonumRoundingUnit"
         "node:lambda:()=>Number.EPSILON / 2"
export
roundingUnit : Double

%foreign "scheme,chez:blodwen-calcFlonumEpsilon"
         "scheme,racket:blodwen-flonumEpsilon"
         "node:lambda:()=>Number.EPSILON"
export
epsilon : Double


%foreign "scheme:blodwen-flonumNaN"
         "node:lambda:()=>Number.NaN"
export
nan : Double


%foreign "scheme:blodwen-flonumInf"
         "node:lambda:()=>Infinity"
export
inf : Double


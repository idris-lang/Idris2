||| Various floating-point number constants
module Data.Double

-- TODO:
--   * nan
--   * inf
--   * docstrings
--   * update changelog

%foreign "scheme:blodwen-calcFlonumRoundingUnit"
         "node:lambda:()=>Number.EPSILON / 2"
public export
roundingUnit : Double

%foreign "scheme,chez:blodwen-calcFlonumEpsilon"
         "scheme,racket:blodwen-flonumEpsilon"
         "node:lambda:()=>Number.EPSILON"
public export
epsilon : Double


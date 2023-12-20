module Data.Primitives.Interpolation

%default total

export Interpolation Int where interpolate = show
export Interpolation Integer where interpolate = show
export Interpolation Bits8 where interpolate = show
export Interpolation Bits16 where interpolate = show
export Interpolation Bits32 where interpolate = show
export Interpolation Bits64 where interpolate = show
export Interpolation Int8 where interpolate = show
export Interpolation Int16 where interpolate = show
export Interpolation Int32 where interpolate = show
export Interpolation Int64 where interpolate = show
export Interpolation Nat where interpolate = show

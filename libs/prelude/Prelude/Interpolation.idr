module Prelude.Interpolation

import Builtin

||| Interpolated strings are of the form `"xxxx \{ expr } yyyy"`.
||| In this example the string `"xxxx "` is concatenated with `expr` and
||| `" yyyy"`, since `expr` is not necessarily a string, the generated
||| code looks like this:
||| ```
||| concat [interpolate "xxxx ", interpolate expr, interpolate " yyyy"]
||| ```
||| This allows to customise the interpolation behaviour by providing
||| an instance of `Interpolation` for a type.
public export
interface Interpolation a where
  constructor MkInterpolation
  interpolate : a -> String

||| The interpolation instance for Strings is the identity
export
Interpolation String where
  interpolate x = x

export
Interpolation Void where
  interpolate _ impossible

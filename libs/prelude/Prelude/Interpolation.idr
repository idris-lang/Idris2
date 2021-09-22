module Prelude.Interpolation

import Prelude.Ops
import Prelude.Types

public export
interface Interpolation a where
  interpolate : a -> String

||| Concatenation of two things with an interpolation strategy.
||| Interpolated strings are of the form `"xxxx \{ expr } yyyy"`.
||| In this example the string `"xxxx "` is concatenated with `expr` and
||| `" yyyy"`, since `expr` is not necessarily a string, the generated
||| code looks like this:
||| ```
||| interpolate "xxxx " ++ interpolate expr ++ interpolate " yyyy"
||| ```
||| This allows to customise the interpolation behaviour by providing
||| an instance of `Interpolation` for a type.
public export
concatInterp : Interpolation a => Interpolation b => a -> b -> String
concatInterp a b = interpolate a ++ interpolate b

||| The interpolation instance for Strings is the identity
export
Interpolation String where
  interpolate x = x

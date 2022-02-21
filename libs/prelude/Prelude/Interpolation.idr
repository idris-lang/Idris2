module Prelude.Interpolation

import Prelude.Show

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
  interpolate : a -> String

||| The interpolation instance for Strings is the identity
public export
[interpId] Interpolation String where
  interpolate x = x

public export
[interpShow] Show a => Interpolation a where
  interpolate x = show x

%hint
%inline
public export
interpDefault : {a : _} -> Show a => Interpolation a
interpDefault {a = String} = interpId
interpDefault {a = _} = interpShow

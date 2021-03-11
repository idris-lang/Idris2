||| N-ary dependent functions using telescopes
|||
||| Compare with `base/Data.Fun` and:
||| Guillaume Allais. 2019. Generic level polymorphic n-ary functions. TyDe 2019.
module Data.Telescope.Fun

import Data.Telescope.Telescope
import Data.Telescope.Segment
import Data.Telescope.SimpleFun

public export
0 Fun : (env : Left.Environment gamma) -> {n : Nat} -> (0 delta : Segment n gamma)
     -> (cod : SimpleFun env delta Type)
     -> Type
Fun env {n = 0  } []            cod = cod
Fun env {n = S n} (ty :: delta) cod = (x : ty env) -> Fun (env ** x) delta (cod x)

public export
uncurry : {0 n : Nat} -> {0 env : Left.Environment gamma} -> {0 delta : Segment n gamma}
       -> {0 cod : SimpleFun env delta Type}
       -> (f : Fun env delta cod) -> (ext : Environment env delta)
       -> uncurry cod ext
uncurry f Empty     = f
uncurry f (x .= xs) = Fun.uncurry (f x) xs

public export
curry : {n : Nat} -> {0 env : Left.Environment gamma} -> {0 delta : Segment n gamma}
     -> {0 cod : SimpleFun env delta Type}
     -> ((ext : Environment env delta) -> SimpleFun.uncurry cod ext)
     -> Fun env delta cod
curry {n = 0  } {delta = []         } f = f Empty
curry {n = S n} {delta = ty :: delta} f = \x => Fun.curry (\xs => f (x .= xs))

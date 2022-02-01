module Data.Linear.Bifunctor

import Data.Linear.Notation

%default total

||| A linear bimap on linear pairs.
||| There is no general Bifunctor interface because it would not be implementable with
||| The same type signature consistently, for example LEither does not consume both
||| `f` and `g` linearly.
export
bimap : (a -@ x) -@ (b -@ y) -@ (LPair a b) -@ (LPair x y)
bimap f g (a # b) = f a # g b

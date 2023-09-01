module B

import Control.Monad.State

import A

public export
X : Type -> Type
X = State AFoo

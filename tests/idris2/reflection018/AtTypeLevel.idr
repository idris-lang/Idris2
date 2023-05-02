module AtTypeLevel

import Control.Monad.State

import Language.Reflection

addName : TTImp -> State (List String) TTImp
addName v@(IVar fc (UN (Basic nm))) = do
    modify (nm ::)
    pure v
addName s = pure s

names : TTImp -> List String
names s = execState [] $ mapMTTImp addName s

checkNames : names `(x * y) = ["y", "x", "*"]
checkNames = Refl


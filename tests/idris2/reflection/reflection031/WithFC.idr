import Language.Reflection

f : List Decl -> Bool
f [IClaim (MkFCVal _ _)] = True
f _ = False

test : f `[x : 1] = True
test = Refl

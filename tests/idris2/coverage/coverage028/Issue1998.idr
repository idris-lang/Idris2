0 proveit : (0 c : Bool) -> c = True
proveit True = Refl

falseIsTrue : False = True
falseIsTrue = irrelevantEq $ proveit False

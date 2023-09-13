module QuoteSearch

import Language.Reflection

%language ElabReflection

x : Elab Nat
x = check `(%search)

defy : Elab ()
defy = do
    let fc = EmptyFC

    val <- quote !x
    logTerm "" 0 "Quoted term:" val

    declare [
        IClaim fc MW Private [] (MkTy fc fc (UN (Basic "y")) (IVar fc (UN (Basic "Nat")))),
        IDef fc (UN (Basic "y")) [PatClause fc (IVar fc (UN (Basic "y"))) (IApp fc (IApp fc (IVar fc (UN (Basic "+"))) val) val)]
    ]

%runElab defy

import Language.Reflection

%language ElabReflection

logPrims : Elab TT
logPrims
    = do ns <- getType `{{ (++) }} 
         traverse (\ (n, ty) =>
                        do logMsg 0 ("Name: " ++ show n)
                           logTerm 0 "Type" ty) ns
         fail "Not really trying"

logDataCons : Elab TT
logDataCons
    = do [(n, _)] <- getType `{{ Nat }}
             | _ => fail "Ambiguous name"
         logMsg 0 ("Resolved name: " ++ show n)
         logMsg 0 ("Constructors: " ++ show !(getCons n))
         fail "Still not trying"

logBad : Elab TT
logBad
    = do [(n, _)] <- getType `{{ DoesntExist }}
             | [] => fail "Undefined name"
             | _ => fail "Ambiguous name"
         logMsg 0 ("Resolved name: " ++ show n)
         logMsg 0 ("Constructors: " ++ show !(getCons n))
         fail "Still not trying"

tryGenSym : Elab TT
tryGenSym
   = do n <- genSym "plus"
        ns <- inCurrentNS n
        fail $ "failed after generating " ++ show ns

dummy1 : a
dummy1 = %runElab logPrims

dummy2 : a
dummy2 = %runElab logDataCons

dummy3 : a
dummy3 = %runElab logBad

dummy4 : a
dummy4 = %runElab tryGenSym


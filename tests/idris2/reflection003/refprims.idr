import Language.Reflection

%language ElabReflection

logPrims : Elab a
logPrims
    = do ns <- getType `{ (++) }
         traverse_ (\ (n, ty) =>
                        do logMsg "" 0 ("Name: " ++ show n)
                           logTerm "" 0 "Type" ty
                           logSugaredTerm "" 0 "Pretty Type" ty
                   ) ns
         fail "Not really trying"

logDataCons : Elab a
logDataCons
    = do [(n, _)] <- getType `{ Nat }
             | _ => fail "Ambiguous name"
         logMsg "" 0 ("Resolved name: " ++ show n)
         logMsg "" 0 ("Constructors: " ++ show !(getCons n))
         fail "Still not trying"

logBad : Elab a
logBad
    = do [(n, _)] <- getType `{ DoesntExist }
             | [] => fail "Undefined name"
             | _ => fail "Ambiguous name"
         logMsg "" 0 ("Resolved name: " ++ show n)
         logMsg "" 0 ("Constructors: " ++ show !(getCons n))
         fail "Still not trying"

-- because the exact sequence number in a gensym depends on
-- the library and compiler internals we need to censor it so the
-- output won't be overly dependent on the exact versions used.
censorDigits : String -> String
censorDigits str = pack $ map (\c => if isDigit c then 'X' else c) (unpack str)

tryGenSym : Elab a
tryGenSym
   = do n <- genSym "plus"
        ns <- inCurrentNS n
        fail $ "failed after generating " ++ censorDigits (show ns)

dummy1 : a
dummy1 = %runElab logPrims

dummy2 : a
dummy2 = %runElab logDataCons

dummy3 : a
dummy3 = %runElab logBad

dummy4 : a
dummy4 = %runElab tryGenSym

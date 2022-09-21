import Language.Reflection

%language ElabReflection

foo : Elab (NameType, NameType, NameType)
foo
  = do [n] <- getInfo `{ Prelude.Nat }
           | _ => fail "Can't find Nat"
       [s] <- getInfo `{ Prelude.S }
           | _ => fail "Can't find S"
       [p] <- getInfo `{ Prelude.plus }
           | _ => fail "Can't find plus"
       pure (nametype (snd n), nametype (snd s), nametype (snd p))

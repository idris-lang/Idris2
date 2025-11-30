import Language.Reflection

matchType : Bool -> Void
matchType Type impossible

matchQuote : Bool -> Void
matchQuote `(1 + 1) impossible

matchCase : Bool -> Void
matchCase (case () of () => ()) impossible

matchLet : Bool -> Void
matchLet (let x = () in x) impossible

matchLocal : Bool -> Void
matchLocal (let x : () in x) impossible

matchSetField : Bool -> Void
matchSetField ({ x := () }) impossible

matchAppField : Bool -> Void
matchAppField ({ x $= () }) impossible

matchWith : Bool -> Void
matchWith (with MkUnit ()) impossible

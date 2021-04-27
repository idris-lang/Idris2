
%default total

-- %logging "compile.casetree" 50
-- %logging "eval.ref" 50
%logging "coverage" 50

test : (String, ()) -> ()
test ("a", ()) = ()

%logging off

test' : (Int, ()) -> ()
test' (1, ()) = ()

test'' : Type -> Type
test'' (List a) = a

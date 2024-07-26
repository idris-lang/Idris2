
data Dict : Type -> Type -> Type where
  DNil : Dict key val
  DCons : key -> val -> Dict key val -> Dict key val

testEmpty : Dict String Nat
testEmpty = [:=]

test1 : Dict String Nat
test1 = [ "hello" := 1 ]

test2 : Dict String Nat
test2 = [ "hello" := 1
        , "world" := 2
        ]

testLet : Dict String Nat
testLet = let x := [ "a" := 3 , "b" := 4 ] in x

testPat : Dict String Nat -> Nat
testPat [:=] = 0
testPat [ k := v ] = 1
testPat (DCons k v rest) = 1 + testPat rest


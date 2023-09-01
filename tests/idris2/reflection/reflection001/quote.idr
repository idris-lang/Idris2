import Language.Reflection

add : TTImp -> TTImp -> TTImp
add x y = `(~(x) + ~(y))

test : TTImp
test = add `(3) `(4)

bigger : TTImp -> TTImp
bigger val
    = `(let xfn : Int -> Int
            xfn var = var * 2 in
            xfn ~(val))

bigger' : Int -> TTImp
bigger' val
    = `(let xfn : Int -> Int
            xfn var = var * 2 in
            xfn ~(IPrimVal EmptyFC (I val)))

bad : Int -> TTImp
bad val
    = `(let xfn : Int -> Int
            xfn var = var * 2 in
            xfn ~(val))

names : List Name
names = [ `{ names }, `{ Prelude.(+) } ]

noExtension : Elab ()
noExtension = fail "Should not print this message"

%runElab noExtension

%language ElabReflection

%runElab noExtension

import Language.Reflection

(.fun) : Nat -> Nat

x : TTImp

f : Nat -> TTImp

useX : TTImp
useX = `(g (~x).fun)

useX' : TTImp
useX' = `(g ~x.fun)

useFX : TTImp
useFX = `(g (~(f 5)).fun)

useFX' : TTImp
useFX' = `(g ~(f 5).fun)

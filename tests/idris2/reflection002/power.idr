import Language.Reflection

%language ElabReflection

powerFn : Nat -> TTImp
powerFn Z = `(const 1)
powerFn (S k) = `(\x => mult x (~(powerFn k) x))

%macro
power : Nat -> Elab TT
power n = check (powerFn n)

cube : Nat -> Nat
cube = power 3

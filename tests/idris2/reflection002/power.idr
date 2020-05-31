import Language.Reflection

%language ElabReflection

powerFn : Nat -> TTImp
powerFn Z = `(const 1)
powerFn (S k) = `(\x => mult x (~(powerFn k) x))

cube : Nat -> Nat
cube = %runElab Check (powerFn 3)

{-
Main> cube 3
27
Main> :printdef cube
Main.cube : Nat -> Nat
cube = \x => mult x (mult x (mult x (const (fromInteger 1) x)))
-}

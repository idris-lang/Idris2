import Language.Reflection

%language ElabReflection

powerFn : Nat -> TTImp
powerFn Z = `(const 1)
powerFn (S k) = `(\x => mult x (~(powerFn k) x))

powerFn' : Nat -> Elab (Nat -> Nat)
powerFn' Z = pure (const 1)
powerFn' (S k) = do powerk <- powerFn' k
                    pure (\x => mult (powerk x) x)

%macro
power : Nat -> Elab (Nat -> Nat)
power n = check (powerFn n)

%macro
power' : Nat -> Elab (Nat -> Nat)
power' n = powerFn' n

cube : Nat -> Nat
cube = power 3

cube' : Nat -> Nat
cube' = power' 3

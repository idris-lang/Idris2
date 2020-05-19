data Bar = MkBar
data Baz = MkBaz

data Vect : Nat -> Type -> Type where
     Nil : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

desc : Type -> String
desc Int = "Int"
desc Nat = "Nat"
desc (Vect n a) = "Vector of " ++ show n ++ " " ++ desc a
desc Type = "Type"
desc _ = "Something else"

descNat : Type -> String
descNat t = "Function from Nat to " ++ desc t

descFn : (x : Type) -> String
descFn ((x : Nat) -> b) = descNat (b Z)
descFn (a -> b) = "Function on " ++ desc a
descFn x = desc x

main : IO ()
main = do printLn (descFn (Nat -> Nat))
          printLn (descFn ((x : Nat) -> Vect x Int))
          printLn (descFn (Type -> Int))

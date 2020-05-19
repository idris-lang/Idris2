identityInt : Int -> Int
identityInt x = x

identityString : String -> String
identityString x = x

identityBool : Bool -> Bool
identityBool x = x

identity : ty -> ty
identity x = x

doubleNat : Nat -> Nat
doubleNat x = x * x

doubleInteger : Integer -> Integer
doubleInteger x = x * x

double : Num ty => ty -> ty
double x = x * x

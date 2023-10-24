data Bool = False | True
data Nat = Z | S Nat

not : Bool -> Bool
not False = True
not True = False

isZero : Nat -> Bool
isZero Z = True
isZero (S k) = False

isOdd : Nat -> Bool
isOdd Z = False
isOdd (S k) = not (isOdd k)

testZ : Nat -> String
testZ x = if isZero x then "Zero" else
             if isOdd x then "Odd" else "Even"

onlyOne : Int -> Int
onlyOne 1 = 2

covered : Int -> Int
covered 1 = 2
covered 2 = 3
covered _ = 94

data IntNat : Integer -> Nat -> Type where
     IsZero : IntNat 0 Z
     IsSuc : IntNat 1 (S k)

-- Only identified as covering if 'x' has multiplicity 0 because then it
-- doesn't show up in the case tree!
matchInt : (0 x : Integer) -> (n : Nat) -> IntNat x n -> String
matchInt 0 Z IsZero = "Zero"
matchInt 1 (S k) IsSuc = "Non Zero"

-- Should be identified as covering but isn't yet since the checker requires
-- a catch all case. This does at least test that the declared 'impossible'
-- case really is impossible; we can update it when the checker improves!
matchInt' : (x : Integer) -> (n : Nat) -> IntNat x n -> String
matchInt' 0 Z IsZero = "Zero"
matchInt' 1 (S k) IsSuc = "Non Zero"
matchInt' 0 (S k) x impossible

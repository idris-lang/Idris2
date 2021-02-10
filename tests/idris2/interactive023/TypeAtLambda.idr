||| Test if :typeat correctly shows types inside lambdas
||| and for lambda arguments

-- Simple lambda
f1 : Nat -> Nat
f1 = (\x => x)

-- Lambda with two arguments
f2 : Nat -> Bool -> (Nat, Bool)
f2 = (\x, b => (x, b))

-- Mixing arguments to the function and to the lambda
f3 : Bool -> Nat -> Int -> (Bool, Nat, Int)
f3 b = (\n, i => (b, n, i))

-- Pattern matching
partial
f4 : Bool -> Nat
f4 = (\True => r)
  where
    -- Create a variable just to test inside the lambda
    r : Nat
    r = 0

-- Pattern matching with pattern variables
partial
f5 : Maybe Bool -> (Bool, Nat)
f5 = (\(Just x) => (x, r))
  where
    r : Nat
    r = 0


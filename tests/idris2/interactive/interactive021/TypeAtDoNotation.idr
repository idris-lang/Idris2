import Data.Vect

||| Test if the type of local variables in do-notation is correctly reported

partial
f : Maybe Nat -> Nat -> Maybe Nat
f x y = do
    -- Bind
    x' <- x

    -- Pattern matching bind
    (S x'') <- x

    -- Let in Do
    let y' = y

    -- Let in Do with pattern matching
    let (S y'') = y

    -- Let in Do with signature
    let a : Nat
        a = x'

    -- Make sure the variable works regardless of how it was bound
    ?result x x' x'' y y' y'' a

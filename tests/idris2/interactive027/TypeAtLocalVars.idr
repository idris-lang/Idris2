import Data.Vect

||| Test if the type of local variables is correctly reported

-- Not meant to be called, just typechecked
partial
f : Nat -> Int -> Bool -> () -> z
f a b c d =

    -- Let with pattern match
    let (S a') = a

        -- Let without signature
        b' = b

        -- Let with signature
        c' : Bool
        c' = c

        -- In the type signature of the Let
        v1 : Vect a Nat
        v1 = ?vect1

    -- After the `in`
    -- It's good to include them all to test that they work regardless
    -- of how they were bound
    in ?result a' b' c' d' v1 v2
  where
    -- Where
    d' : ()
    d' = d

    -- In the type signature of the Where
    v2 : Vect x Nat
    v2 = ?vect2


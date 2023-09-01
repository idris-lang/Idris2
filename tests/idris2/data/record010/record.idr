-- This test ensures that implicits bound on the RHS of a
-- record update field are correctly bound by the compiler.


record Rec where
    n : Nat


data T : Rec -> Type where
    C : T ({ n := Z } r)


data U : Rec -> Type where
    D : U ({ n $= S } r)

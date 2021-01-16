nat_induction :
    (prop : Nat -> Type) ->                -- Property to show
    (prop Z) ->                            -- Base case
    ((k : Nat) -> prop k -> prop (S k)) -> -- Inductive step
    (x : Nat) ->                           -- Show for all x
    prop x
nat_induction prop p_Z p_S Z = p_Z
nat_induction prop p_Z p_S (S k) = p_S k (nat_induction prop p_Z p_S k)

plus_ind : Nat -> Nat -> Nat
plus_ind n m
   = nat_induction (\x => Nat)
                   m                      -- Base case, plus_ind Z m
                   (\k, k_rec => S k_rec) -- Inductive step plus_ind (S k) m
                                          -- where k_rec = plus_ind k m
                   n


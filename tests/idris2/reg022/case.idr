-- Previously this gave an 'unreachable case warning' and evaluated
-- to the first case! Should give foo : Nat -> Nat
foo : (x : Nat) -> case S x of
                        Z => Nat -> Nat
                        (S k) => Nat

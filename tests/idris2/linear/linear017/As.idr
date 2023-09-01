-- Reduction of https://gist.github.com/AlgebraicWolf/0d921915d7aca032e35831c73c8d04f4

-- See Discord discussion for further context:
-- https://discord.com/channels/827106007712661524/954409815088721920/1108129142756606102

data X : Nat -> Type where
  IZ : X Z
  IS : (0 n : _) -> X n -> X (S n)

g : (m : Nat) -> X m -> Nat

g (S m@(S m')) (IS .(S m') k) = g (S m') k
g _ _ = 0

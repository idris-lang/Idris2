module Issue2712

-- a non-dependent indexed state monad, à la TDD Ch 13+14
data ISM : Type -> Nat -> Nat -> Type where
  CMD_INIT : (n : Nat) -> ISM () n n
  CMD_INCR : ISM () n (S n)

  Pure : (x : t) -> ISM t n n
  (>>=) :  ISM a from to
        -> ISM b to to2
        -> ISM b from to2

-- this should be considered covering
foo : ISM a st st -> ()   -- note the fixed 'to' and 'from' state
foo (CMD_INIT n) = ?foo_rhs_0
foo (Pure x) = ?foo_rhs_2
foo (x >>= f) = ?foo_rhs_3

failing "Cycle detected in solution of metavariable"
  foo' : ISM a st st -> ()   -- note the fixed 'to' and 'from' state
  foo' (CMD_INIT n) = ?foo_bis_rhs_0
  foo' CMD_INCR = ?foo_bis_rhs_1
  foo' (Pure x) = ?foo_bis_rhs_2
  foo' (x >>= f) = ?foo_bis_rhs_3


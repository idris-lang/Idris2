import Data.Vect

%unbound_implicits off

append : forall n, m, a . Vect n a -> Vect m a -> Vect (n + m) a
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

data Env : forall n . Vect n Type -> Type where
     ENil : Env []
     ECons : forall t, ts . t -> Env ts -> Env (t :: ts)

-- fine because the only name used in bound, and it'll infer types for
-- xs and its indices
len : forall xs . Env xs -> Nat

-- neither of these are fine
len': Env xs -> Nat
append' : Vect n a -> Vect m a -> Vect (n + m) a

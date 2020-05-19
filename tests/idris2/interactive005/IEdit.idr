data Vect : Nat -> Type -> Type where
     Nil : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

%name Vect xs, ys, zs

my_cong : forall f . (x : a) -> (y : a) -> x = y -> f x = f y

my_curry : ((a, b) -> c) -> a -> b -> c

my_uncurry : (a -> b -> c) -> (a, b) -> c

append : Vect n a -> Vect m a -> Vect (n + m) a

lappend : (1 xs : List a) -> (1 ys : List a) -> List a

zipWith : (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c

data Env : Vect n Type -> Type where
     ENil : Env []
     ECons : a -> Env xs -> Env (a :: xs)

%name Env es

data Elem : a -> Vect n a -> Type where
     Here : Elem x (x :: xs)
     There : (p : Elem x xs) -> Elem x (y :: xs)

lookup : Elem ty vs -> Env vs -> ty

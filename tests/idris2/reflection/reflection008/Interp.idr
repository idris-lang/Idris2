import Data.Vect
import Data.Fin
import Language.Reflection

%language ElabReflection

data Ty : Type where
     Base : Type -> Ty
     Arrow : Ty -> Ty -> Ty

-- Ty can be translated to a host language type

interpTy : Ty -> Type
interpTy (Base t) = t
interpTy (Arrow s t) = (argTy : interpTy s) -> interpTy t

data HasType : Fin k -> Ty -> Vect k Ty -> Type where
     Stop : HasType FZ t (t :: gam)
     Pop  : HasType i t gam -> HasType (FS i) t (u :: gam)

data Lang : Vect k Ty -> Ty -> Type where
     Var : HasType i t gam -> Lang gam t
     Val : (x : interpTy a) -> Lang gam a
     Lam : (scope : Lang (s :: gam) t) -> Lang gam (Arrow s t)
     App : Lang gam (Arrow s t) -> Lang gam s -> Lang gam t;
     Op  : (interpTy a -> interpTy b -> interpTy c) ->
           Lang gam a -> Lang gam b -> Lang gam c

data Env : Vect n Ty -> Type where
     Nil : Env Nil
     (::) : (x : interpTy a) -> Env xs -> Env (a :: xs)

-- Find a value in an environment
lookupEnv : HasType i t gam -> Env gam -> Elab (interpTy t)
lookupEnv Stop (x :: xs) = pure x
lookupEnv (Pop var) (x :: env) = lookupEnv var env

interp : Env gam -> Lang gam t -> Elab (interpTy t)
interp env (Var x)
    = do res <- lookupEnv x env
         pure res
interp env (Val x) = pure x
interp env (Lam scope)
    = lambda _ (\val => interp (val :: env) scope)
interp env (App f a)
    = interp env f <*> interp env a
interp env (Op f x y) = f <$> interp env x <*> interp env y

%macro
eval : Env gam -> Lang gam t -> Elab (interpTy t)
eval = interp

testAdd : Lang gam (Arrow (Base Nat) (Arrow (Base Nat) (Base Nat)))
testAdd = Lam (Lam (Op plus (Var Stop) (Var (Pop Stop))))

evalAdd : Nat -> Nat -> Nat
evalAdd x y =let add = eval [] testAdd in add x y

testBlock : Lang gam (Base Nat)
testBlock = Op {a=Base Nat} {b=Base Nat} plus (Val 3) (Val 4)

evalBlock : Nat
evalBlock = eval [] testBlock

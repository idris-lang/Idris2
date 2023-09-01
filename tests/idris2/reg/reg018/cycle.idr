import Data.Vect
import Data.Vect.Elem

data Typ : Type where
    TLam : Typ -> Typ -> Typ
    TNat : Typ

data Term : Typ -> Vect len Typ -> Type where
    Var : Elem a ctx -> Term a ctx
    Lam : Term b (a :: ctx) -> Term (TLam a b) ctx
    Fix : Term a (a :: ctx) -> Term a ctx

lookup : Vect len Typ -> Fin len -> Typ
lookup (a :: ctx) FZ = a
lookup (_ :: ctx) (FS n) = lookup ctx n

count : {ctx : Vect len Typ} -> (n : Fin len) -> Elem (lookup ctx n) ctx
count {ctx = _ :: ctx} FZ = Here
count {ctx = _ :: ctx} (FS n) = There (count n)

segfaults : {len : _} -> {ctx : Vect len Typ} ->
            Term (TLam TNat TNat) ctx
segfaults = Fix (Lam (Var (count 0)))

cycleDetected : {len : _} -> {ctx : Vect len Typ} ->
                Term (TLam TNat TNat) ctx
cycleDetected = Fix (Var (count 0))

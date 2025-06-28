
import Data.Vect

record Container where
  typebind constructor MkCont
  base : Type
  fibre : base -> Type

%hide Prelude.(&&)

export
typebind
Exists : (t : Type) -> (t -> Type) -> Type
Exists = DPair

ListCont : Container
ListCont = MkCont (n : Nat) | Fin n

val2 : Exists Nat (\n => Vect n Nat)
val2 = (4 ** [0,1,2,3])

typebind
record Σ (t : Type) (s : t -> Type) where
  constructor (&&)
  π1 : t
  π2 : s π1

(=>>) : (t : Type) -> (t -> Type) -> Type
(=>>) a b = (x : a) -> b x

private typebind infixr 0 =>>

autobind
loop : Applicative f => Foldable t => t a -> (a -> f b) -> f ()
loop = Prelude.for_

val : Exists (n : Nat) | Vect n Nat
val = (4 ** [0,1,2,3])

main : IO ()
main = loop (x := [0 .. 10]) |
         printLn x

sigmaPi : Σ (ty : Type) | (x : ty) =>> Type
sigmaPi = (Type && List)

nestedSigma : Σ (ty : Type) | Σ (n : Nat) | Vect n ty
nestedSigma = (String && 2 && ["hello", "world"])



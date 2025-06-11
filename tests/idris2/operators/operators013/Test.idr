
import Data.Vect

export
typebind
Exists : (t : Type) -> (t -> Type) -> Type
Exists = DPair

val : Exists (n : Nat) | Vect n Nat
val = (4 ** [0,1,2,3])

-- val2 : Exists Nat (\n => Vect n Nat)
-- val2 = (4 ** [0,1,2,3])

autobind
for : Applicative f => Foldable t => t a -> (a -> f b) -> f ()
for = Prelude.for_

main : IO ()
main = for (x := [0 .. 10]) |
         printLn x

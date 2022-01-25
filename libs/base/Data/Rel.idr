module Data.Rel

import Data.Fun

%default total

||| Build an n-ary relation type from a Vect of Types
public export
Rel : Vect n Type -> Type
Rel ts = Fun ts Type

||| Universal quantification of a n-ary Relation over its
||| arguments to build a (function) type from a `Rel` type
|||
||| ```
||| λ> All [Nat,Nat] LTE
||| (x : Nat) -> (x : Nat) -> LTE x x
||| ```
public export
All : (ts : Vect n Type) -> (p : Rel ts) -> Type
All [] p = p
All (t :: ts) p = (x : t) -> All ts (p x)

||| Existential quantification of a n-ary relation over its
||| arguments to build a dependent pair (eg. Sigma type).
|||
||| Given a (type of) relation `p : [t_1, t_2 ... t_n] x r` where `t_i` and `r` are
||| types, `Ex` builds the type `Σ (x_1 : t_1). Σ (x_2 : t_2) ... . r`
||| For example:
||| ```
||| λ> Ex [Nat,Nat] LTE
||| (x : Nat ** (x : Nat ** LTE x x))
||| ```
||| Which is the type of a pair of natural numbers along with a proof that the first
||| is smaller or equal than the second.
public export
Ex : (ts : Vect n Type) -> (p : Rel ts) -> Type
Ex [] p = p
Ex (t :: ts) p = (x : t ** Ex ts (p x))

||| Map a type-level function over the co-domain of a n-ary Relation
public export
liftRel : (ts : Vect n Type) -> (p : Rel ts) -> (Type -> Type) -> Type
liftRel ts p f = All ts $ map @{Nary} f p

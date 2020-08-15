module Data.Rel

import Data.Fun

||| Build an n-ary relation type from a Vect of Types
public export
Rel : Vect n Type -> Type
Rel ts = Fun ts Type

||| Universal quantification of a n-ary Relation over its
||| arguments to build a (function) type from a `Rel` type
public export
All : (ts : Vect n Type) -> (p : Rel ts) -> Type
All [] p = p
All (t :: ts) p = (x : t) -> All ts (p x)

||| Map a type-level function over the co-domain of a n-ary Relation
public export
liftRel : (ts : Vect n Type) -> (p : Rel ts) -> (Type -> Type) -> Type
liftRel ts p f = All ts $ map @{Nary} f p

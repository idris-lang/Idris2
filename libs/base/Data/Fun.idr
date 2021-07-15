module Data.Fun

import public Data.Vect

%default total

||| Build an n-ary function type from a Vect of Types and a result type
public export
Fun : Vect n Type -> Type -> Type
Fun [] r = r
Fun (t::ts) r = t -> Fun ts r

public export
chain : {ts : Vect n Type} -> Fun [r] r' -> Fun ts r -> Fun ts r'
chain {ts = []} g r  = g r
chain {ts = (_::_)} g f = \ x => chain g (f x)

public export
[Nary] {ts : Vect n Type} -> Functor (Fun ts) where
  map = chain

||| Returns the co-domain of a n-ary function.
public export
target : {ts : Vect n Type} -> {r: Type} -> Fun ts r -> Type
target _ = r

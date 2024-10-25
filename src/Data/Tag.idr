module Data.Tag

import public Data.List.Quantifiers
import public Data.List.Elem
import public Decidable.Equality
import public Data.Singleton

%hide Builtin.infixr.(#)

export prefix 3 #

-- A possible tag is any one instance of a singleton
-- picked from the list of candidates
public export
(#) : List String -> Type
(#) xs = Any Singleton xs

public export
OneOf : List String -> Type
OneOf xs = Any Singleton xs

-- Show instances for singleton and any
public export
Show (Singleton {a = String} x) where
  show (Val x) = x

export
(xs : List String) => Show (Any Singleton xs) where
  show {xs = a :: as} (Here x) = show x
  show {xs = a :: as} (There x) = show x


-- Evidence that a decidable property is satisfied
public export
data IsYes : Dec a -> Type where
  Witness : (w : a) -> IsYes (Yes w)

-- Given that we have a witness for a decidable property, extract it
public export
extract : {x : Dec a} -> IsYes x -> a
extract (Witness w) = w

-- Given a string, and evidence that the string belongs to a list of strings `xs`
-- return the membership proof as an instance of Any
public export
mkE : (s : String) -> Elem s xs -> #xs
mkE s Here = Here (Val s)
mkE s (There x) = There $ mkE s x

-- Convert string literals by computing the proof that the given string actually
-- exists in the list of candidates. If that is the case, extract the inhabitant
-- from the proof.
public export
fromString : (s : String) -> {xs : List String} ->
             (e : IsYes (s `isElem` xs)) => #xs
fromString s {e} = mkE s (extract e)


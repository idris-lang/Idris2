module Data.Choice

import Data.Tag
import Data.List.Elem

export infix 0 :-

public export
(:-) : String -> Type -> (String, Type)
(:-) = MkPair

public export
ChoiceOf : List (String, Type) -> Type
ChoiceOf xs = Any id (map snd xs)

-- Given a string, and evidence that the string belongs to a list of strings `xs`
-- return the membership proof as an instance of Any
public export
mkE : (s : String) -> {xs : List (String, Type)} -> Elem s (map Builtin.fst xs) -> ChoiceOf xs
mkE _ {xs = []} _ impossible
mkE s {xs = ((s, ty) :: xs)} (Here {x = s}) = Here ?aa
mkE s {xs = (y :: xs)} (There x) = There $ mkE s {xs} x

-- Convert string literals by computing the proof that the given string actually
-- exists in the list of candidates. If that is the case, extract the inhabitant
-- from the proof.
public export
fromString : (s : String) -> {xs : List (String, Type)} ->
             (e : IsYes (s `isElem` map Builtin.fst xs)) => ChoiceOf xs
fromString s {e} = mkE s (extract e)



import Data.String

typebind infixr 0 :-
autobind infixr 0 `for`

record Container where
  constructor (:-)
  a1 : Type
  a2 : a1 -> Type

const : Type -> Type -> Container
const a b = (_ : a) :- b

test : Maybe (List Double)
test = (_ := ["1", "two", "3"]) `for` Just 3

test2 : Maybe (List Double)
test2 = (_ : String := ["1", "two", "3"]) `for` Just 3

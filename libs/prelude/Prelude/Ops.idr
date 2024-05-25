module Prelude.Ops

-- Numerical operators
export infix 6 ==, /=, <, <=, >, >=
export infixl 8 +, -
export infixl 9 *, /

-- Boolean operators
export infixr 5 &&
export infixr 4 ||

-- List and String operators
export infixr 7 ::, ++
export infixl 7 :<

-- Equivalence
export infix 0 <=>

-- Functor/Applicative/Monad/Algebra operators
export infixl 1 >>=, =<<, >>, >=>, <=<, <&>
export infixr 2 <|>
export infixl 3 <*>, *>, <*
export infixr 4 <$>, $>, <$
export infixl 8 <+>

-- Utility operators
export infixr 9 ., .:
export infixr 0 $, <|
export infixl 0 |>

export infixl 9 `div`, `mod`

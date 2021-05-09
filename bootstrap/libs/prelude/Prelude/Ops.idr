module Prelude.Ops

-- Numerical operators
infix 6 ==, /=, <, <=, >, >=
infixl 8 +, -
infixl 9 *, /

-- Boolean operators
infixr 5 &&
infixr 4 ||

-- List and String operators
infixr 7 ::, ++

-- Functor/Applicative/Monad/Algebra operators
infixl 1 >>=, =<<, >>, >=>, <=<, <&>
infixr 2 <|>
infixl 3 <*>, *>, <*
infixr 4 <$>, $>, <$
infixl 8 <+>

-- Utility operators
infixr 9 ., .:
infixr 0 $

infixl 9 `div`, `mod`

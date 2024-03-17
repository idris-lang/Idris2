||| Until Idris2 starts supporting the 'syntax' keyword, here's a
||| poor-man's equational reasoning
module Syntax.PreorderReasoning

import public Syntax.PreorderReasoning.Ops

|||Slightly nicer syntax for justifying equations:
|||```
||| |~ a
||| ~~ b ...( justification )
|||```
|||and we can think of the `...( justification )` as ASCII art for a thought bubble.
public export
data Step : a -> b -> Type where
  (...) : (0 y : a) -> (0 step : x ~=~ y) -> Step x y

public export
data FastDerivation : (x : a) -> (y : b) -> Type where
  (|~) : (0 x : a) -> FastDerivation x x
  (~~) : FastDerivation x y -> (step : Step y z) -> FastDerivation x z

public export
Calc : {0 x : a} -> {0 y : b} -> (0 der : FastDerivation x y) -> x ~=~ y
Calc der = irrelevantEq $ Calc' der
  where
    Calc' : {0 x : c} -> {0 y : d} -> FastDerivation x y -> x ~=~ y
    Calc' (|~ x) = Refl
    Calc' ((~~) der (_ ...(Refl))) = Calc' der

{- -- requires import Data.Nat
0
example : (x : Nat) -> (x + 1) + 0 = 1 + x
example x =
  Calc $
   |~ (x + 1) + 0
   ~~ x+1  ...( plusZeroRightNeutral $ x + 1 )
   ~~ 1+x  ...( plusCommutative x 1          )
-}

-- Smart constructors
public export
(..<) : (0 y : a) -> {0 x : b} -> (0 step : y ~=~ x) -> Step x y
(y ..<(prf)) {x} = (y ...(sym prf))

public export
(..>) : (0 y : a) -> (0 step : x ~=~ y) -> Step x y
(..>) = (...)

||| Use a judgemental equality but is not trivial to the reader.
public export
(~=) : FastDerivation x y -> (0 z : dom) -> {auto 0 xEqy : y = z} -> FastDerivation x z
(~=) der y {xEqy = Refl} = der ~~ y ... Refl

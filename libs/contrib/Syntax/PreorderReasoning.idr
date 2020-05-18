|||  Until Idris2 starts supporting the 'syntax' keyword, here's a
|||  poor-man's equational reasoning
module Syntax.PreorderReasoning

||| Deep embedding of equation derivation sequences.
||| Using the Nil, (::) constructors lets us use list syntax.
public export
data Derivation : (x : a) -> (y : b) -> Type where
  Nil : Derivation x x
  (::) : (x = y) -> Derivation y z -> Derivation x z
  
infix 1 ==|

||| Explicate the term under consideration and the justification for
||| the next step.
export
(==|) : (x : a) -> (x = y) -> x = y
(==|) x pf = pf

||| Finishg the derivation.
||| A bit klunky, but this /is/ a poor-man's version.
export
QED : {x : a} -> x = x
QED = Refl

export
Calculate : Derivation x y -> x = y
Calculate [] = Refl
Calculate (Refl :: der) = Calculate der

{--
||| Requires Data.Nata
example : (x : Nat) -> (x + 1) + 0 = 1 + x
example x = Calculate [
  (x + 1) + 0 
  ==| plusZeroRightNeutral (x + 1) ,
  x + 1
  ==| plusCommutative x 1 ,
  1 + x  
  ==| QED
  ]
--}

module Syntax.PreorderReasoning.Generic

import Decidable.Order
infixl 0  ~~
infixl 0  <~
prefix 1  |~
infix  1  ...

public export
data Step : (leq : a -> a -> Type) -> a -> a -> Type where
  (...) : (y : a) -> x `leq` y -> Step leq x y

public export
data FastDerivation : (leq : a -> a -> Type) -> (x : a) -> (y : a) -> Type where
  (|~) : (x : a) -> FastDerivation leq x x
  (<~) : {x, y : a}
         -> FastDerivation leq x y -> {z : a} -> (step : Step leq y z)
         -> FastDerivation leq x z

public export
CalcWith : Preorder dom leq => {x,y : dom} -> FastDerivation leq x y -> x `leq` y
CalcWith (|~ x) = reflexive x
CalcWith ((<~) der (z ... step)) = transitive {po = leq} _ _ _ (CalcWith der) step

public export
(~~) : {x,y : dom}
         -> FastDerivation leq x y -> {z : dom} -> (step : Step Equal y z)
         -> FastDerivation leq x z
(~~) der (z ... Refl) = der

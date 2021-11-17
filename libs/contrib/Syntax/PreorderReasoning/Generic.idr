module Syntax.PreorderReasoning.Generic

import Control.Relation
import Control.Order
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
CalcWith : Preorder dom leq => {0 x : dom} -> {0 y : dom} -> FastDerivation leq x y -> x `leq` y
CalcWith (|~ x) = reflexive {rel = leq}
CalcWith ((<~) der (z ... step)) = transitive {rel = leq} (CalcWith der) step

public export
(~~) : {0 x : dom} -> {0 y : dom}
         -> FastDerivation leq x y -> {z : dom} -> (step : Step Equal y z)
         -> FastDerivation leq x z
(~~) der (z ... Refl) = der

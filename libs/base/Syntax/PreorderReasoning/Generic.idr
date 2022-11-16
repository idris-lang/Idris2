module Syntax.PreorderReasoning.Generic

import Control.Relation
import Control.Order
infixl 0  ~~, ~=
infixl 0  <~
prefix 1  |~
infix  1  ...,..<,..>,.=.,.=<,.=>

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
data DerivationType = TrivialDerivation | NonTrivialDerivation

public export
derivationType : FastDerivation leq x y -> DerivationType
derivationType (|~ x) = TrivialDerivation
derivationType (z <~ step) = NonTrivialDerivation

public export
interface CalcType (0 dom : Type) (0 leq : dom -> dom -> Type) (derivType : DerivationType) where
  CalcKnown : {0 x, y : dom} -> (deriv : FastDerivation leq x y) -> {auto derivTypeEq : derivationType deriv = derivType}  -> x `leq` y

public export
Reflexive dom leq => CalcType dom leq TrivialDerivation where
  CalcKnown (|~ _) {derivTypeEq = Refl} = reflexive
  CalcKnown (_ <~ _) impossible

public export
Transitive dom leq => CalcType dom leq NonTrivialDerivation where
  CalcKnown (|~ _) impossible
  CalcKnown ((|~ _) <~ (_ ... step)) = step
  CalcKnown (deriv@(_ <~ _) <~ (_ ... step)) = CalcKnown deriv `transitive` step

public export
CalcWith : Preorder dom leq => {0 x : dom} -> {0 y : dom} -> FastDerivation leq x y -> x `leq` y
CalcWith (|~ x) = CalcKnown (|~ x)
CalcWith ((<~) der (z ... step)) = CalcKnown (der <~ z ... step)

public export
(~~) : {0 x : dom} -> {0 y : dom}
         -> FastDerivation leq x y -> {z : dom} -> (step : Step Equal y z)
         -> FastDerivation leq x z
(~~) der (z ... Refl) = der

-- Smart constructors
public export
(..<) : Symmetric a leq => (y : a) -> {x : a} -> y `leq` x -> Step leq x y
(y ..<(prf)) {x} = (y ...(symmetric prf))

public export
(..>) : (y : a) -> x `leq` y -> Step leq x y
(..>) = (...)

public export
(.=.) : Reflexive a leq  => (y : a) -> {x : a} ->
    x === y -> Step leq x y
(y .=.(Refl)) {x = _} = (y ...(reflexive))

public export
(.=>) : Reflexive a leq  => (y : a) -> {x : a} ->
    x === y -> Step leq x y
(.=>) = (.=.)

public export
(.=<) : Reflexive a leq  => (y : a) -> {x : a} ->
    y === x -> Step leq x y
(y .=<(Refl)) = (y ...(reflexive))

public export
(~=) : FastDerivation rel x y -> (z : dom) -> {auto xEqy : y = z} -> FastDerivation rel x z
(~=) deriv _ {xEqy = Refl} = deriv

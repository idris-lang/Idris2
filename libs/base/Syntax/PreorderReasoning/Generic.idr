module Syntax.PreorderReasoning.Generic

import Control.Relation
import Control.Order
import public Syntax.PreorderReasoning.Ops

public export
data Step : (leq : a -> a -> Type) -> a -> a -> Type where
  (...) : (y : a) -> x `leq` y -> Step leq x y

public export
data FastDerivation : (leq : a -> a -> Type) -> (x : a) -> (y : a) -> Type where
  (|~) : (x : a) -> FastDerivation leq x x
  (<~) : {x, y : a}
         -> FastDerivation leq x y -> {0 z : a} -> (step : Step leq y z)
         -> FastDerivation leq x z

-- Using a McKinna-McBride view records the depenencies on the type of derivation
-- the additional benefits for pattern-matching aren't used here
public export
data DerivationType : FastDerivation leq x y -> Type where
  TrivialDerivation : DerivationType (|~ x)
  SingleStepDerivation : DerivationType (|~ x <~ step)
  NonTrivialDerivation : DerivationType (der <~ step1 <~ step2)

public export
derivationType : (der : FastDerivation leq x y) -> DerivationType der
derivationType (|~ x) = TrivialDerivation
derivationType (|~ x <~ step) = SingleStepDerivation
derivationType ((z <~ w) <~ step) = NonTrivialDerivation

public export
0 Prerequisite : {0 der : FastDerivation {a = dom} leq x y} -> DerivationType der -> Type
Prerequisite TrivialDerivation = Reflexive dom leq
Prerequisite SingleStepDerivation = ()
Prerequisite NonTrivialDerivation = Transitive dom leq

-- Once we have the prerequisite for transitivity, we have the
-- prerequisite for its inductive predecessor:
public export
inductivePrerequisite : (der : FastDerivation leq x y) ->
  (0 step1 : Step leq y z) -> (0 step2 : Step leq z w) ->
  Prerequisite (derivationType (der <~ step1 <~ step2)) ->
  Prerequisite (derivationType (der <~ step1))
inductivePrerequisite (  |~ y    ) step1 step2 prerequisite = ()
inductivePrerequisite (z <~ step0) step1 step2 prerequisite = prerequisite

public export
preorderPrerequisite : Preorder dom leq => (der : FastDerivation leq x y) -> Prerequisite (derivationType der)
preorderPrerequisite (|~ x) = %search
preorderPrerequisite (|~ x <~ step) = ()
preorderPrerequisite (der <~ step1 <~ step2) = %search

||| The Prerequisite for the derivation:
||| 0-length derivation: Reflexive dom leq
||| 1-length derivation: Unit (no prerequisite)
||| 2 steps of longer: Transitivity
public export
CalcSmart : {0 x : dom} -> {0 y : dom} -> (der : FastDerivation leq x y) ->
  Prerequisite (derivationType der) => x `leq` y
CalcSmart (|~ x) = reflexive
CalcSmart (|~ x <~ y ... step) = step
CalcSmart (der <~ _ ... step1
               <~ w ... step2) @{prereq} =
                CalcSmart (der <~ _ ... step1)
                @{inductivePrerequisite der (_ ... step1) (w ... step2) prereq}
                  `transitive` step2

public export
CalcWith : Preorder dom leq => {0 x : dom} -> {0 y : dom} -> (der : FastDerivation leq x y) -> x `leq` y
CalcWith der = CalcSmart der @{preorderPrerequisite der}

public export
(~~) : {0 x : dom} -> {0 y : dom}
         -> FastDerivation leq x y -> {0 z : dom} -> (0 step : Step Equal y z)
         -> FastDerivation leq x z
(~~) der (z ... yEqZ) = replace {p = FastDerivation leq _} yEqZ der

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
(~=) : FastDerivation leq x y -> (0 z : dom) -> {auto xEqy : y = z} -> FastDerivation leq x z
(~=) der z {xEqy} = der ~~ z ...(xEqy)

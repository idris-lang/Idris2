||| Division theorem for (type-level) natural number division
module Data.Nat.Division

import Syntax.WithProof
import Syntax.PreorderReasoning
import Syntax.PreorderReasoning.Generic
import Data.Nat
import Data.Nat.Equational
import Data.Nat.Order
import Data.Nat.Order.Strict
import Decidable.Equality
import Decidable.Order
import Decidable.Order.Strict

%default total

-- Need a few more facts about order
-- The converse to lteIsLTE:
LteIslte : (a, b : Nat) -> a `LTE` b -> a `lte` b = True
                          -- DYI Syntax.PreorderReasoning from contrib
LteIslte  a b a_lt_b with (the (x : Bool ** a `lte` b = x) (a `lte` b ** Refl))
 LteIslte a b a_lt_b | (True  ** prf) = prf
 LteIslte a b a_lt_b | (False ** prf) = void $ irreflexive {spo = Data.Nat.LT} a 
   $ CalcWith {leq = LTE} $
   |~ 1 + a
   <~ 1 + b  ...(plusLteMonotoneLeft 1 a b a_lt_b)
   <~ a      ...(notlteIsLT _ _ prf)

-- The converse to lteIsLTE:
GTIsnotlte : (a, b : Nat) -> b `LT` a -> a `lte` b = False
                          -- DYI Syntex.PreorderReasoning from contrib
GTIsnotlte  a b b_lt_a with (the (x : Bool ** a `lte` b = x) (a `lte` b ** Refl))
 GTIsnotlte a b b_lt_a | (False ** prf) = prf
 GTIsnotlte a b b_lt_a | (True  ** prf) = void $ irreflexive {spo = Data.Nat.LT} b 
   $ CalcWith {leq = LTE} $
   |~ 1 + b
   <~ a  ...(b_lt_a)
   <~ b  ...(lteIsLTE _ _ prf)

||| Subtracting a number gives a smaller number
export
minusLTE : (a,b : Nat) -> (b `minus` a) `LTE` b
minusLTE a      0    = LTEZero
minusLTE 0     (S b) = reflexive (S b)
minusLTE (S a) (S b) = transitive (minus b a) b (S b)
                         (minusLTE a b)
                         (lteSuccRight (reflexive b))

||| Subtracting a positive number gives a strictly smaller number
export
minusPosLT : (a,b : Nat) -> 0 `LT` a -> a `LTE` b -> (b `minus` a) `LT` b
minusPosLT 0     b     z_lt_z           a_lte_b impossible
minusPosLT (S a) 0     z_lt_sa          a_lte_b impossible
minusPosLT (S a) (S b) z_lt_sa          a_lte_b = LTESucc (minusLTE a b)


multRightCancel : (a,b,r : Nat) -> Not (r = 0) -> a*r = b*r -> a = b
multRightCancel a      b    0           r_nz ar_eq_br = void $ r_nz Refl
multRightCancel 0      0    r@(S predr) r_nz ar_eq_br = Refl
multRightCancel 0     (S b) r@(S predr) r_nz ar_eq_br impossible
multRightCancel (S a)  0    r@(S predr) r_nz ar_eq_br impossible
multRightCancel (S a) (S b) r@(S predr) r_nz ar_eq_br = 
  cong S $ multRightCancel a b r r_nz 
         $ plusLeftCancel r (a*r) (b*r) ar_eq_br

-- This is the opposite of the convention in `Data.Nat`, but 'monotone on the left' means the below
multLteMonotoneRight : (l, a, b : Nat) -> a `LTE` b -> l*a `LTE` l*b
multLteMonotoneRight  0    a b _ = LTEZero
multLteMonotoneRight (S k) a b a_lte_b = CalcWith {leq = LTE} $
  |~ (1 + k) * a
  ~~ a +  k*a    ...(Refl)
  <~ b +  k*a    ...(plusLteMonotoneRight (k*a) a b a_lte_b)
  <~ b +  k*b    ...(plusLteMonotoneLeft  b (k*a) (k*b) $
                     multLteMonotoneRight k    a     b   a_lte_b)
  ~~ (1 + k) * b ...(Refl)

multLteMonotoneLeft : (a, b, r : Nat) -> a `LTE` b -> a*r `LTE` b*r
multLteMonotoneLeft a b r a_lt_b = 
  rewrite multCommutative a r in
  rewrite multCommutative b r in
  multLteMonotoneRight r a b a_lt_b


-- Division theorem --------------------
-- This is disgusting, but will do for now

||| Show that, if we have enough fuel, we have enough fuel for the
||| recursive call in `div'` and `mod'`.
fuelLemma : (numer, predDenom, fuel : Nat) 
          -> (enough : numer `LTE` (S fuel))
          -> (recurse : Data.Nat.lte numer predDenom = False)
          -> (numer `minus` (S predDenom)) `LTE` fuel
fuelLemma numer predDenom fuel enough recurse =
  let denom  : Nat
      denom = S predDenom
      numer' : Nat
      numer' = numer `minus` denom
      -- a bunch of inequational reasoning to show we have enough fuel
      -- on the recursive call
      denom_lte_numer : denom `LTE` numer
      denom_lte_numer = notlteIsLT numer predDenom recurse
      numer'_lt_numer : numer' `LT` numer
      numer'_lt_numer = (minusPosLT denom numer 
                          (LTESucc LTEZero)
                          denom_lte_numer)
      succenough : S numer' `LTE` S fuel
      succenough = transitive (S numer') numer (S fuel)
                              numer'_lt_numer
                              enough
  in fromLteSucc succenough

divisionTheorem' : (numer, predDenom : Nat)
                -> (fuel : Nat) -> (enough : numer `LTE` fuel)
                -> numer = (mod' fuel numer predDenom) + (div' fuel numer predDenom) * (S predDenom)
 
divisionTheorem'  0     predDenom  0       LTEZero = Refl
divisionTheorem'  numer predDenom (S fuel) enough with (@@(Data.Nat.lte numer predDenom))
 divisionTheorem' numer predDenom (S fuel) enough | (True ** prf)
   = rewrite prf in
     rewrite plusZeroRightNeutral numer in Refl
 divisionTheorem' numer predDenom (S fuel) enough | (False ** prf)
   = rewrite prf in 
     let denom  : Nat
         denom = S predDenom
         numer' : Nat
         numer' = numer `minus` denom
         denom_lte_numer : denom `LTE` numer
         denom_lte_numer = notlteIsLT numer predDenom prf
         enough' : numer' `LTE` fuel 
         enough' = fuelLemma numer predDenom fuel enough prf
         
         inductionHypothesis : (numer' 
                             = (mod' fuel numer' predDenom) +  (div' fuel numer' predDenom) * denom)
         inductionHypothesis = divisionTheorem' numer' predDenom fuel enough'
     in sym $ Calc $
     |~ (mod' fuel numer' predDenom) + (denom + (div' fuel numer' predDenom) * denom)
     ~~ (mod' fuel numer' predDenom) + ((div' fuel numer' predDenom) * denom + denom)
              ...(cong ((mod' fuel numer' predDenom) +) $ plusCommutative 
                                                          denom
                                                          ((div' fuel numer' predDenom) * denom))
     ~~((mod' fuel numer' predDenom) +  (div' fuel numer' predDenom) * denom) + denom
              ...(plusAssociative 
                    (mod' fuel numer' predDenom)
                    ((div' fuel numer' predDenom) * denom)
                    denom)
     ~~ numer' + denom ...(cong (+ denom) $ sym inductionHypothesis)
     ~~ numer ...(plusMinusLte denom numer denom_lte_numer)



export
DivisionTheorem : (numer, denom : Nat) -> (prf1, prf2 : Not (denom = Z))
               -> numer = (modNatNZ numer denom prf1) + (divNatNZ numer denom prf2)*denom
DivisionTheorem numer 0 prf1 prf2 = void (prf1 Refl)
DivisionTheorem numer (S predDenom) prf1 prf2 
  = divisionTheorem' numer predDenom numer (reflexive numer) 
    
    
modZeroZero : (denom, fuel : Nat)
           -> mod' fuel 0 denom = 0
modZeroZero denom  0       = Refl
modZeroZero denom (S fuel) = Refl

modFuelLemma : (numer, denom, fuel1, fuel2 : Nat) 
            -> (enough1 : fuel1 `GTE` numer) 
            -> (enough2 : fuel2 `GTE` numer)
            -> mod' fuel1 numer denom = mod' fuel2 numer denom
modFuelLemma  0 denom 0 fuel2 LTEZero enough2 = rewrite modZeroZero denom fuel2 in Refl
modFuelLemma  0 denom (S fuel1) 0 enough1 LTEZero = Refl
modFuelLemma  numer denom (S fuel1) (S fuel2) enough1 enough2 with (@@(Data.Nat.lte numer denom))
 modFuelLemma numer denom (S fuel1) (S fuel2) enough1 enough2 | (True  ** prf)  = 
   rewrite prf in Refl
 modFuelLemma numer denom (S fuel1) (S fuel2) enough1 enough2 | (False ** prf) = 
   rewrite prf in 
   modFuelLemma (numer `minus` (S denom)) denom fuel1 fuel2
     (fuelLemma numer denom fuel1 enough1 prf) 
     (fuelLemma numer denom fuel2 enough2 prf) 



multiplicationLemma : (q, predn, r : Nat) -> q * (S predn) + r `LTE` 0 -> (q = 0, r = 0)
multiplicationLemma q predn r bound = 
  let r_eq_z : (r = 0)
      r_eq_z = zeroPlusRightZero (q * (S predn)) r (sym $ lteZeroIsZero bound)
      qn_eq_z : (q * (S predn) = 0)
      qn_eq_z = zeroPlusLeftZero (q * (S predn)) r (sym $ lteZeroIsZero bound)
      q_eq_z : q = 0
      q_eq_z = case zeroMultEitherZero q (S predn) qn_eq_z of
        Left  q_eq_0 => q_eq_0
        Right spred_eq_z impossible
  in (q_eq_z, r_eq_z)


multiplesModuloZero : (fuel, predn, k : Nat) 
       -> (enough : fuel `GTE` k * (S predn) )
       -> mod' fuel (k * (S predn)) predn = 0
multiplesModuloZero 0        predn k enough = 
  let (k_eq_z, _) = multiplicationLemma k predn 0 
                    rewrite plusZeroRightNeutral (k * (S predn)) in 
                    enough
  in rewrite k_eq_z in 
  Refl
multiplesModuloZero  (S fuel) predn 0 enough = Refl
multiplesModuloZero  (S fuel) predn (S k) enough = 
  let n : Nat
      n = S predn
      n_lte_skn : n `LTE` (1 + k)*n
      n_lte_skn = CalcWith {leq = LTE} $ 
        |~ n
        ~~ n  + 0     ...(sym $ plusZeroRightNeutral n)
        ~~ (1 + 0)*n ...(Refl)
        <~ (1 + k)*n   ...(multLteMonotoneLeft (1+0) (1+k) n $ 
                           plusLteMonotoneLeft 1 0 k LTEZero)
  in case @@(Data.Nat.lte ((1 + k)*n) predn) of
    (True  ** skn_lte_predn) => absurd $ irreflexive {spo = Data.Nat.LT} predn 
                                       $ CalcWith {leq = LTE} $
      |~ 1 + predn
      ~~ n         ...(Refl)
      ~~ n + 0     ...(sym $ plusZeroRightNeutral n)
      ~~ (1 + 0)*n ...(Refl)
      <~ (1 + k)*n ...(multLteMonotoneLeft (1+0) (1+k) n $ 
                       LTESucc LTEZero)
      <~ predn     ...(lteIsLTE _ _ skn_lte_predn)
    (False ** prf) => 
      rewrite prf in 
      let skn_minus_n_eq_kn : ((1 + k)*n `minus` n = k*n)
          skn_minus_n_eq_kn = Calc $
            |~ ((1+k)*n `minus` n)
            ~~ ((1+k)*n `minus` (n + 0)) ...(cong ((1+k)*n `minus`) $ sym $ plusZeroRightNeutral n)
            ~~ (n + k*n `minus` (n + 0)) ...(Refl)
            ~~ (k*n `minus` 0)           ...(plusMinusLeftCancel n (k*n) 0)
            ~~ k*n                       ...(minusZeroRight (k*n))
      in rewrite skn_minus_n_eq_kn in 
      multiplesModuloZero fuel predn k $
      (rewrite sym $ skn_minus_n_eq_kn in 
       fuelLemma ((1 + k)*n) predn fuel enough prf)
    
-- We also want to show uniqueness of this decomposition
-- This is, of course, quite horrible, but I want this theorem in the stdlib
addMultipleMod': (fuel1, fuel2, predn, a, b : Nat) -> (enough1 : fuel1 `GTE` b * (S predn) + a)
                                           -> (enough2 : fuel2 `GTE` a)
       -> mod' fuel1 (b * (S predn) + a) predn = mod' fuel2 a predn
addMultipleMod' 0         fuel2 predn a b enough1 enough2 
  = let (b_eq_z, a_eq_z) = multiplicationLemma b predn a enough1
    in rewrite a_eq_z in
       rewrite b_eq_z in
       rewrite modZeroZero predn fuel2 in
       Refl
addMultipleMod' fuel1@(S _) fuel2 predn a 0 enough1 enough2 = 
  modFuelLemma a predn fuel1 fuel2 enough1 enough2
addMultipleMod' (S fuel1) fuel2 predn a (S k) enough1 enough2 =
  let n : Nat
      n = S predn
      lhsarg_geq_predn : ((1 + k)*n + a) `GT` predn
      lhsarg_geq_predn = CalcWith {leq = LTE} $
        |~ n
        ~~ (1+0)*n     ...(sym $ plusZeroRightNeutral n)
        <~ (1+k)*n     ...(multLteMonotoneLeft 1 (1+k) n $
                           LTESucc LTEZero)
        <~ (1+k)*n + a ...(lteAddRight $ (1+k)*n)
      prf1 : lte ((1 + k)*n + a) predn = False
      prf1 = GTIsnotlte ((1 + k)*n + a) predn lhsarg_geq_predn
      argsimplify : (((1 + k) *n + a ) `minus` n = k*n + a)
      argsimplify = Calc $
        |~ (((1+k)*n + a) `minus` n)
        ~~ (((n + k*n) + a) `minus` n)       ...(Refl)
        ~~ ((n + (k*n + a)) `minus` (n + 0)) ...(cong2 minus
                                                   (sym $ plusAssociative n (k*n) a)
                                                   (sym $ plusZeroRightNeutral n))
        ~~ ((k*n + a) `minus` 0)             ...(plusMinusLeftCancel n (k*n + a) 0)
        ~~ k*n + a                           ...(minusZeroRight (k*n + a))
  in rewrite prf1 in
     rewrite argsimplify in 
     addMultipleMod' fuel1 fuel2 predn a k 
       (rewrite sym argsimplify in 
        fuelLemma ((1+k)*n + a) predn fuel1 enough1 prf1)
       enough2

addMultipleMod : (a, b, n : Nat) -> (n_neq_z1, n_neq_z2 : Not (n = 0))
              -> modNatNZ (a*n + b) n n_neq_z1 = modNatNZ b n n_neq_z2
addMultipleMod a b 0           n_neq_z1  n_neq_z2 = void (n_neq_z1 Refl)
addMultipleMod a b n@(S predn) n_neq_z1  n_neq_z2 = 
  addMultipleMod' (a*n + b) b predn b a (reflexive {po = LTE} _) (reflexive {po = LTE} _)

modBelowDenom : (r, n : Nat) -> (n_neq_z : Not (n = 0))
             -> (r `LT` n) 
             -> modNatNZ r n n_neq_z  = r
modBelowDenom 0 (S predn) n_neq_0 (LTESucc r_lte_predn) = Refl
modBelowDenom r@(S _) (S predn) n_neq_0 (LTESucc r_lte_predn) = 
  rewrite LteIslte r predn r_lte_predn in
  Refl

modInjective : (r1, r2, n : Nat) -> (n_neq_z1, n_neq_z2 : Not (n = 0))
             -> (r1 `LT` n) 
             -> (r2 `LT` n)
             -> modNatNZ r1 n n_neq_z1  = modNatNZ r2 n n_neq_z2
             -> r1 = r2
modInjective r1 r2 n n_neq_z1 n_neq_z2 r1_lt_n r2_lt_n ri_mod_eq = Calc $
  |~ r1
  ~~ modNatNZ r1 n n_neq_z1 ...(sym $ modBelowDenom r1 n n_neq_z1 r1_lt_n)
  ~~ modNatNZ r2 n n_neq_z2 ...(ri_mod_eq)
  ~~ r2                     ...(      modBelowDenom r2 n n_neq_z2 r2_lt_n)


step1 : (numer : Nat) -> (denom : Nat) -> (denom_nz : Not (denom = 0))
     -> (q, r : Nat) -> (r `LT` denom) -> (numer = q * denom + r)
     -> modNatNZ numer denom denom_nz = r
step1 x n n_nz q r r_lt_n x_eq_qnpr = Calc $
  |~ modNatNZ x         n n_nz
  ~~ modNatNZ (q*n + r) n n_nz ...(cong (\u => modNatNZ u n n_nz) $ x_eq_qnpr)
  ~~ modNatNZ r         n n_nz ...(addMultipleMod q r n n_nz n_nz)
  ~~ r                         ...(modBelowDenom r n n_nz r_lt_n)


step2 : (numer : Nat) -> (denom : Nat) -> (denom_nz : Not (denom = 0))
     -> (q, r : Nat) -> (r `LT` denom) -> (numer = q * denom + r)
     -> divNatNZ numer denom denom_nz = q
step2 x n n_nz q r r_lt_n x_eq_qnr = 
  let mod_eq_r : (modNatNZ x n n_nz = r)
      mod_eq_r = step1 x n n_nz q r r_lt_n x_eq_qnr
      
      two_decompositions : divNatNZ x n n_nz * n + r = q * n + r
      two_decompositions = Calc $
        |~ divNatNZ x n n_nz * n + r
        ~~ divNatNZ x n n_nz * n + (modNatNZ x n n_nz) ...(cong (divNatNZ x n n_nz * n +) 
                                                              $ sym mod_eq_r)
        ~~ modNatNZ x n n_nz + divNatNZ x n n_nz * n   ...(plusCommutative _ _)
        ~~ x                                           ...(sym $ DivisionTheorem x n n_nz n_nz)
        ~~ q*n + r                                     ...(x_eq_qnr)
        
  in multRightCancel (divNatNZ x n n_nz) q n n_nz
   $ plusRightCancel (divNatNZ x n n_nz * n) (q*n) r
   $ two_decompositions

export
DivisionTheoremUniqueness : (numer : Nat) -> (denom : Nat) -> (denom_nz : Not (denom = 0))
     -> (q, r : Nat) -> (r `LT` denom) -> (numer = q * denom + r)
     -> (divNatNZ numer denom denom_nz = q, modNatNZ numer denom denom_nz = r)
DivisionTheoremUniqueness numer denom denom_nz q r x prf = 
  (step2 numer denom denom_nz q r x prf, step1 numer denom denom_nz q r x prf)

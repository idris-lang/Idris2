module Data.Nat

export
Uninhabited (Z = S n) where
  uninhabited Refl impossible

export
Uninhabited (S n = Z) where
  uninhabited Refl impossible

public export
isZero : Nat -> Bool
isZero Z     = True
isZero (S n) = False

public export
isSucc : Nat -> Bool
isSucc Z     = False
isSucc (S n) = True

public export
data IsSucc : (n : Nat) -> Type where
  ItIsSucc : IsSucc (S n)

export
Uninhabited (IsSucc Z) where
  uninhabited ItIsSucc impossible

public export
isItSucc : (n : Nat) -> Dec (IsSucc n)
isItSucc Z = No absurd
isItSucc (S n) = Yes ItIsSucc

public export
power : Nat -> Nat -> Nat
power base Z       = S Z
power base (S exp) = base * (power base exp)

public export
hyper : Nat -> Nat -> Nat -> Nat
hyper Z        a b      = S b
hyper (S Z)    a Z      = a
hyper (S(S Z)) a Z      = Z
hyper n        a Z      = S Z
hyper (S pn)   a (S pb) = hyper pn a (hyper (S pn) a pb)

public export
pred : Nat -> Nat
pred Z     = Z
pred (S n) = n

-- Comparisons

public export
data NotBothZero : (n, m : Nat) -> Type where
  LeftIsNotZero  : NotBothZero (S n) m
  RightIsNotZero : NotBothZero n     (S m)

public export
data LTE  : (n, m : Nat) -> Type where
  LTEZero : LTE Z    right
  LTESucc : LTE left right -> LTE (S left) (S right)

export
Uninhabited (LTE (S n) Z) where
  uninhabited LTEZero impossible

public export
GTE : Nat -> Nat -> Type
GTE left right = LTE right left

public export
LT : Nat -> Nat -> Type
LT left right = LTE (S left) right

public export
GT : Nat -> Nat -> Type
GT left right = LT right left

export
succNotLTEzero : Not (LTE (S m) Z)
succNotLTEzero LTEZero impossible

export
fromLteSucc : LTE (S m) (S n) -> LTE m n
fromLteSucc (LTESucc x) = x

export
isLTE : (m, n : Nat) -> Dec (LTE m n)
isLTE Z n = Yes LTEZero
isLTE (S k) Z = No succNotLTEzero
isLTE (S k) (S j)
    = case isLTE k j of
           No contra => No (contra . fromLteSucc)
           Yes prf => Yes (LTESucc prf)

export
lteRefl : {n : Nat} -> LTE n n
lteRefl {n = Z}   = LTEZero
lteRefl {n = S k} = LTESucc lteRefl

export
lteSuccRight : LTE n m -> LTE n (S m)
lteSuccRight LTEZero     = LTEZero
lteSuccRight (LTESucc x) = LTESucc (lteSuccRight x)

export
lteSuccLeft : LTE (S n) m -> LTE n m
lteSuccLeft (LTESucc x) = lteSuccRight x

export
lteTransitive : LTE n m -> LTE m p -> LTE n p
lteTransitive LTEZero y = LTEZero
lteTransitive (LTESucc x) (LTESucc y) = LTESucc (lteTransitive x y)

export
lteAddRight : (n : Nat) -> LTE n (n + m)
lteAddRight Z = LTEZero
lteAddRight (S k) {m} = LTESucc (lteAddRight {m} k)

export
notLTImpliesGTE : {a, b : _} -> Not (LT a b) -> GTE a b
notLTImpliesGTE {b = Z} _ = LTEZero
notLTImpliesGTE {a = Z} {b = S k} notLt = absurd (notLt (LTESucc LTEZero))
notLTImpliesGTE {a = S k} {b = S j} notLt = LTESucc (notLTImpliesGTE (notLt . LTESucc))

public export
lte : Nat -> Nat -> Bool
lte Z        right     = True
lte left     Z         = False
lte (S left) (S right) = lte left right

public export
gte : Nat -> Nat -> Bool
gte left right = lte right left

public export
lt : Nat -> Nat -> Bool
lt left right = lte (S left) right

public export
gt : Nat -> Nat -> Bool
gt left right = lt right left

public export
minimum : Nat -> Nat -> Nat
minimum Z m = Z
minimum (S n) Z = Z
minimum (S n) (S m) = S (minimum n m)

public export
maximum : Nat -> Nat -> Nat
maximum Z m = m
maximum (S n) Z = S n
maximum (S n) (S m) = S (maximum n m)

-- Proofs on S

export
eqSucc : (left : Nat) -> (right : Nat) -> (p : left = right) ->
         S left = S right
eqSucc left _ Refl = Refl

export
succInjective : (left : Nat) -> (right : Nat) -> (p : S left = S right) ->
                left = right
succInjective left _ Refl = Refl

export
SIsNotZ : (S x = Z) -> Void
SIsNotZ Refl impossible

export
modNatNZ : Nat -> (y: Nat) -> Not (y = Z) -> Nat
modNatNZ left Z         p = void (p Refl)
modNatNZ left (S right) _ = mod' left left right
  where
    mod' : Nat -> Nat -> Nat -> Nat
    mod' Z        centre right = centre
    mod' (S left) centre right =
      if lte centre right then
        centre
      else
        mod' left (minus centre (S right)) right

export
modNat : Nat -> Nat -> Nat
modNat left (S right) = modNatNZ left (S right) SIsNotZ

export
divNatNZ : Nat -> (y: Nat) -> Not (y = Z) -> Nat
divNatNZ left Z         p = void (p Refl)
divNatNZ left (S right) _ = div' left left right
  where
    div' : Nat -> Nat -> Nat -> Nat
    div' Z        centre right = Z
    div' (S left) centre right =
      if lte centre right then
        Z
      else
        S (div' left (minus centre (S right)) right)

export
divNat : Nat -> Nat -> Nat
divNat left (S right) = divNatNZ left (S right) SIsNotZ

export
divCeilNZ : Nat -> (y: Nat) -> Not (y = Z) -> Nat
divCeilNZ x y p = case (modNatNZ x y p) of
  Z   => divNatNZ x y p
  S _ => S (divNatNZ x y p)

export
divCeil : Nat -> Nat -> Nat
divCeil x (S y) = divCeilNZ x (S y) SIsNotZ

public export
Integral Nat where
  div = divNat
  mod = modNat

export
gcd : (a: Nat) -> (b: Nat) -> {auto ok: NotBothZero a b} -> Nat
gcd a Z     = a
gcd Z b     = b
gcd a (S b) = gcd (S b) (modNatNZ a (S b) SIsNotZ)

export
lcm : Nat -> Nat -> Nat
lcm _ Z     = Z
lcm Z _     = Z
lcm a (S b) = divNat (a * (S b)) (gcd a (S b))

--------------------------------------------------------------------------------
-- An informative comparison view
--------------------------------------------------------------------------------
public export
data CmpNat : Nat -> Nat -> Type where
     CmpLT : (y : _) -> CmpNat x (x + S y)
     CmpEQ : CmpNat x x
     CmpGT : (x : _) -> CmpNat (y + S x) y

export
total cmp : (x, y : Nat) -> CmpNat x y
cmp Z Z     = CmpEQ
cmp Z (S k) = CmpLT _
cmp (S k) Z = CmpGT _
cmp (S x) (S y) with (cmp x y)
  cmp (S x) (S (x + (S k))) | CmpLT k = CmpLT k
  cmp (S x) (S x)           | CmpEQ   = CmpEQ
  cmp (S (y + (S k))) (S y) | CmpGT k = CmpGT k

-- Proofs on

export
plusZeroLeftNeutral : (right : Nat) -> 0 + right = right
plusZeroLeftNeutral right = Refl

export
plusZeroRightNeutral : (left : Nat) -> left + 0 = left
plusZeroRightNeutral Z     = Refl
plusZeroRightNeutral (S n) =
  let inductiveHypothesis = plusZeroRightNeutral n in
    rewrite inductiveHypothesis in Refl

export
plusSuccRightSucc : (left : Nat) -> (right : Nat) ->
  S (left + right) = left + (S right)
plusSuccRightSucc Z right        = Refl
plusSuccRightSucc (S left) right =
  let inductiveHypothesis = plusSuccRightSucc left right in
    rewrite inductiveHypothesis in Refl

export
plusCommutative : (left : Nat) -> (right : Nat) ->
  left + right = right + left
plusCommutative Z        right = rewrite plusZeroRightNeutral right in Refl
plusCommutative (S left) right =
  let inductiveHypothesis = plusCommutative left right in
    rewrite inductiveHypothesis in
      rewrite plusSuccRightSucc right left in Refl

export
plusAssociative : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  left + (centre + right) = (left + centre) + right
plusAssociative Z        centre right = Refl
plusAssociative (S left) centre right =
  let inductiveHypothesis = plusAssociative left centre right in
    rewrite inductiveHypothesis in Refl

export
plusConstantRight : (left : Nat) -> (right : Nat) -> (c : Nat) ->
  (p : left = right) -> left + c = right + c
plusConstantRight left _ c Refl = Refl

export
plusConstantLeft : (left : Nat) -> (right : Nat) -> (c : Nat) ->
  (p : left = right) -> c + left = c + right
plusConstantLeft left _ c Refl = Refl

export
plusOneSucc : (right : Nat) -> 1 + right = S right
plusOneSucc n = Refl

export
plusLeftCancel : (left : Nat) -> (right : Nat) -> (right' : Nat) ->
  (p : left + right = left + right') -> right = right'
plusLeftCancel Z        right right' p = p
plusLeftCancel (S left) right right' p =
  let inductiveHypothesis = plusLeftCancel left right right' in
    inductiveHypothesis (succInjective _ _ p)

export
plusRightCancel : (left : Nat) -> (left' : Nat) -> (right : Nat) ->
  (p : left + right = left' + right) -> left = left'
plusRightCancel left left' Z         p = rewrite sym (plusZeroRightNeutral left) in
                                         rewrite sym (plusZeroRightNeutral left') in
                                                 p
plusRightCancel left left' (S right) p =
  plusRightCancel left left' right
    (succInjective _ _ (rewrite plusSuccRightSucc left right in
                        rewrite plusSuccRightSucc left' right in p))

export
plusLeftLeftRightZero : (left : Nat) -> (right : Nat) ->
  (p : left + right = left) -> right = Z
plusLeftLeftRightZero Z        right p = p
plusLeftLeftRightZero (S left) right p =
  plusLeftLeftRightZero left right (succInjective _ _ p)

-- Proofs on *

export
multZeroLeftZero : (right : Nat) -> Z * right = Z
multZeroLeftZero right = Refl

export
multZeroRightZero : (left : Nat) -> left * Z = Z
multZeroRightZero Z        = Refl
multZeroRightZero (S left) = multZeroRightZero left

export
multRightSuccPlus : (left : Nat) -> (right : Nat) ->
  left * (S right) = left + (left * right)
multRightSuccPlus Z        right = Refl
multRightSuccPlus (S left) right =
  let inductiveHypothesis = multRightSuccPlus left right in
    rewrite inductiveHypothesis in
    rewrite plusAssociative left right (left * right) in
    rewrite plusAssociative right left (left * right) in
    rewrite plusCommutative right left in
            Refl

export
multLeftSuccPlus : (left : Nat) -> (right : Nat) ->
  (S left) * right = right + (left * right)
multLeftSuccPlus left right = Refl

export
multCommutative : (left : Nat) -> (right : Nat) ->
  left * right = right * left
multCommutative Z right        = rewrite multZeroRightZero right in Refl
multCommutative (S left) right =
  let inductiveHypothesis = multCommutative left right in
      rewrite inductiveHypothesis in
      rewrite multRightSuccPlus right left in
              Refl

export
multDistributesOverPlusRight : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  left * (centre + right) = (left * centre) + (left * right)
multDistributesOverPlusRight Z        centre right = Refl
multDistributesOverPlusRight (S left) centre right =
  let inductiveHypothesis = multDistributesOverPlusRight left centre right in
    rewrite inductiveHypothesis in
    rewrite plusAssociative (centre + (left * centre)) right (left * right) in
    rewrite sym (plusAssociative centre (left * centre) right) in
    rewrite plusCommutative (left * centre) right in
    rewrite plusAssociative centre right (left * centre) in
    rewrite plusAssociative (centre + right) (left * centre) (left * right) in
            Refl

export
multDistributesOverPlusLeft : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  (left + centre) * right = (left * right) + (centre * right)
multDistributesOverPlusLeft Z        centre right = Refl
multDistributesOverPlusLeft (S left) centre right =
  let inductiveHypothesis = multDistributesOverPlusLeft left centre right in
    rewrite inductiveHypothesis in
    rewrite plusAssociative right (left * right) (centre * right) in
            Refl

export
multAssociative : (left : Nat) -> (centre : Nat) -> (right : Nat) ->
  left * (centre * right) = (left * centre) * right
multAssociative Z        centre right = Refl
multAssociative (S left) centre right =
  let inductiveHypothesis = multAssociative left centre right in
    rewrite inductiveHypothesis in
    rewrite multDistributesOverPlusLeft centre (left * centre) right in
            Refl

export
multOneLeftNeutral : (right : Nat) -> 1 * right = right
multOneLeftNeutral Z         = Refl
multOneLeftNeutral (S right) =
  let inductiveHypothesis = multOneLeftNeutral right in
    rewrite inductiveHypothesis in
            Refl

export
multOneRightNeutral : (left : Nat) -> left * 1 = left
multOneRightNeutral Z        = Refl
multOneRightNeutral (S left) =
  let inductiveHypothesis = multOneRightNeutral left in
    rewrite inductiveHypothesis in
            Refl

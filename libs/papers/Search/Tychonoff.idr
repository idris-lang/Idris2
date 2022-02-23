||| This module is based on Todd Waugh Ambridge's blog post series
||| "Search over uniformly continuous decidable predicates on
||| infinite collections of types"
||| https://www.cs.bham.ac.uk/~txw467/tychonoff/InfiniteSearch1.html

module Search.Tychonoff

import Data.DPair
import Data.Nat
import Data.Nat.Order
import Data.So
import Decidable.Equality
import Decidable.Decidable

%default total

------------------------------------------------------------------------------
-- Searchable types
------------------------------------------------------------------------------

Pred : Type -> Type
Pred a = a -> Type

0 Decidable : Pred a -> Type
Decidable p = (x : a) -> Dec (p x)

||| A type is searchable if for any
||| p a decidable predicate over that type
||| x can be found such that if there exists a
||| x0 satisfying p then x also satisfies p
0 IsSearchable : Type -> Type
IsSearchable a
  = (0 p : Pred a) -> Decidable p ->
    (x : a ** (x0 : a) -> p x0 -> p x)

infix 0 <->
record (<->) (a, b : Type) where
  constructor MkIso
  forwards  : a -> b
  backwards : b -> a
  inverseL  : (x : a) -> backwards (forwards x) === x
  inverseR  : (y : b) -> forwards (backwards y) === y

||| Searchable is closed under isomorphisms
map : (a <-> b) -> IsSearchable a -> IsSearchable b
map (MkIso f g _ inv) search p pdec =
  let (xa ** prfa) = search (p . f) (\ x => pdec (f x)) in
  (f xa ** \ xb, pxb => prfa (g xb) $ replace {p} (sym $ inv xb) pxb)

interface Searchable (0 a : Type) where
  search : IsSearchable a

Inhabited : Type -> Type
Inhabited a = a

SearchableIsInhabited : IsSearchable a -> Inhabited a
SearchableIsInhabited search = fst (search (\ _ => ()) (\ _ => Yes ()))

-- Finite types are trivially searchable

||| Unit is searchable
Searchable () where
  search p pdef = (() ** \ (), prf => prf)

||| Bool is searchable
Searchable Bool where
  search p pdec = case pdec True of
    -- if p True holds we're done
    Yes prf   => MkDPair True $ \ _, _ => prf
    -- otherwise p False is our best bet
    No contra => MkDPair False $ \case
      False => id
      True  => absurd . contra

||| Searchable is closed under finite sum
-- Note that this would enable us to go back and prove Bool searchable
-- via the iso Bool <-> Either () ()
(Searchable a, Searchable b) => Searchable (Either a b) where
  search p pdec =
    let (xa ** prfa) = search (p . Left) (\ xa => pdec (Left xa)) in
    let (xb ** prfb) = search (p . Right) (\ xb => pdec (Right xb)) in
    case pdec (Left xa) of
      Yes pxa => (Left xa ** \ _, _ => pxa)
      No npxa => case pdec (Right xb) of
        Yes pxb => (Right xb ** \ _, _ => pxb)
        No npxb => MkDPair (Left xa) $ \case
          Left xa' => \ pxa' => absurd (npxa (prfa xa' pxa'))
          Right xb' => \ pxb' => absurd (npxb (prfb xb' pxb'))

||| Searchable is closed under finite product
(Searchable a, Searchable b) => Searchable (a, b) where
  search p pdec =
    -- How cool is that use of choice?
    let (fb ** prfb) = Pair.choice $ \ a => search (p . (a,)) (\ b => pdec (a, b)) in
    let (xa ** prfa) = search (\ a => p (a, fb a)) (\ xa => pdec (xa, fb xa)) in
    MkDPair (xa, fb xa) $ \ (xa', xb'), pxab' => prfa xa' (prfb xa' xb' pxab')

||| The usual LPO is for Nat only
0 LPO : Type -> Type
LPO a = (f : a -> Bool) ->
        Either (x : a ** f x === True) ((x : a) -> f x === False)

0 LPO' : Type -> Type
LPO' a = (0 p : Pred a) -> Decidable p ->
         Either (x : a ** p x) ((x : a) -> Not (p x))

SearchableIsLPO : IsSearchable a -> LPO' a
SearchableIsLPO search p pdec =
  let (x ** prf) = search p pdec in
  case pdec x of
    Yes px => Left (x ** px)
    No npx => Right (\ x', px' => absurd (npx (prf x' px')))

LPOIsSearchable : LPO' a -> Inhabited a -> IsSearchable a
LPOIsSearchable lpo inh p pdec = case lpo p pdec of
  Left (x ** px) => (x ** \ _, _ => px)
  Right contra   => (inh ** \ x, px => absurd (contra x px))

EqUntil : (m : Nat) -> (a, b : Nat -> x) -> Type
EqUntil m a b = (k : Nat) -> k `LTE` m -> a k === b k

record UniformlyContinuous {x : Type} (p : (Nat -> x) -> Type) where
  constructor MkUC
  uniformBound : Nat
  uniformContinuity : (a, b : Nat -> x) -> EqUntil uniformBound a b -> p a -> p b

------------------------------------------------------------------------------
-- Closeness functions and extended naturals
------------------------------------------------------------------------------

||| A decreasing sequence of booleans
Decreasing : (Nat -> Bool) -> Type
Decreasing f = (n : Nat) -> So (f (S n)) -> So (f n)

||| Nat extended with a point at infinity
record NatInf where
  constructor MkNatInf
  sequence     : Nat -> Bool
  isDecreasing : Decreasing sequence

repeat : x -> (Nat -> x)
repeat v = const v

Zero : NatInf
Zero = MkNatInf (repeat False) (\ n, prf => prf)

Omega : NatInf
Omega = MkNatInf (repeat True) (\ n, prf => prf)

(::) : x -> (Nat -> x) -> (Nat -> x)
(v :: f) 0 = v
(v :: f) (S n) = f n

Succ : NatInf -> NatInf
Succ f = MkNatInf (True :: f .sequence) decr where

  decr : Decreasing (True :: f .sequence)
  decr 0     = const Oh
  decr (S n) = f .isDecreasing n

fromNat : Nat -> NatInf
fromNat 0 = Zero
fromNat (S k) = Succ (fromNat k)

soFromNat : k `LT` n -> So ((fromNat n) .sequence k)
soFromNat p = case view p of
  LTZero => Oh
  LTSucc p => soFromNat p

fromNatSo : {k, n : Nat} -> So ((fromNat n) .sequence k) -> k `LT` n
fromNatSo {n = 0} hyp = absurd hyp
fromNatSo {k = 0} {n = S n} hyp = LTESucc LTEZero
fromNatSo {k = S k} {n = S n} hyp = LTESucc (fromNatSo hyp)

LTE : (f, g : NatInf) -> Type
f `LTE` g = (n : Nat) -> So (f .sequence n) -> So (g .sequence n)

minimalZ : (f : NatInf) -> fromNat 0 `LTE` f
minimalZ f n prf = absurd prf

maximalInf : (f : NatInf) -> f `LTE` Omega
maximalInf f n prf = Oh

min : (f, g : NatInf) -> NatInf
min (MkNatInf f prf) (MkNatInf g prg)
  = MkNatInf (\ n => f n && g n) $ \ n, prfg =>
    let (l, r) = soAnd prfg in
    andSo (prf n l, prg n r)

minLTE : (f, g : NatInf) -> min f g `LTE` f
minLTE (MkNatInf f prf) (MkNatInf g prg)  n pr = fst (soAnd pr)

max : (f, g : NatInf) -> NatInf
max (MkNatInf f prf) (MkNatInf g prg)
  = MkNatInf (\ n => f n || g n) $ \ n, prfg =>
    orSo $ case soOr prfg of
      Left pr => Left (prf n pr)
      Right pr => Right (prg n pr)

maxLTE : (f, g : NatInf) -> f `LTE` max f g
maxLTE (MkNatInf f prf) (MkNatInf g prg) n pr = orSo (Left pr)

record ClosenessFunction (0 x : Type) (c : (v, w : x) -> NatInf) where
  constructor MkClosenessFunction
  selfClose  : (v : x) -> c v v === Omega
  closeSelf  : (v, w : x) -> c v w === Omega -> v === w
  symmetric  : (v, w : x) -> c v w === c w v
  ultrametic : (u, v, w : x) -> min (c u v) (c v w) `LTE` c u w

------------------------------------------------------------------------------
-- Discrete closeness function
------------------------------------------------------------------------------

Discrete : Type -> Type
Discrete = DecEq

dc : Discrete x => (v, w : x) -> NatInf
dc v w = ifThenElse (isYes $ decEq v w) Omega Zero

dcIsClosenessFunction : Discrete x => ClosenessFunction x Tychonoff.dc
dcIsClosenessFunction
  = MkClosenessFunction selfClose closeSelf symmetric ultrametric

  where

  selfClose : (v : x) -> dc v v === Omega
  selfClose v with (decEq v v)
    _ | Yes pr = Refl
    _ | No npr = absurd (npr Refl)

  closeSelf : (v, w : x) -> dc v w === Omega -> v === w
  closeSelf v w eq with (decEq v w)
    _ | Yes pr = pr
    _ | No npr = absurd (cong (($ 0) . sequence) eq)

  symmetric : (v, w : x) -> dc v w === dc w v
  symmetric v w with (decEq v w)
    symmetric v v | Yes Refl = rewrite decEqSelfIsYes {x = v} in Refl
    _ | No nprf with (decEq w v)
      _ | Yes prf = absurd (nprf (sym prf))
      _ | No _ = Refl

  ultrametric : (u, v, w : x) -> min (dc u v) (dc v w) `LTE` dc u w
  ultrametric u v w n with (decEq u w)
    _ | Yes r = const Oh
    _ | No nr with (decEq u v)
      _ | Yes p with (decEq v w)
        _ | Yes q = absurd (nr (trans p q))
        _ | No nq = id
      _ | No np with (decEq v w)
        _ | Yes q = id
        _ | No nq = id

------------------------------------------------------------------------------
-- Discrete-sequence closeness function
------------------------------------------------------------------------------

decEqUntil : Discrete x => (n : Nat) -> (f, g : Nat -> x) -> Dec (EqUntil n f g)
decEqUntil n f g = decideLTEBounded (\ n => decEq (f n) (g n)) n

fromYes : (d : Dec p) -> isYes d === True -> p
fromYes (Yes prf) _ = prf

decEqUntilPred :
  Discrete x => (n : Nat) -> (f, g : Nat -> x) ->
  isYes (decEqUntil (S n) f g) === True ->
  isYes (decEqUntil n     f g) === True
decEqUntilPred n f g eq with (decEqUntil n f g)
  _ | Yes prf = Refl
  _ | No nprf = let prf = fromYes (decEqUntil (S n) f g) eq in
                absurd (nprf $ \ l, bnd => prf l (lteSuccRight bnd))

public export
dsc : Discrete x => (f, g : Nat -> x) -> NatInf
dsc f g = (MkNatInf Meas decr) where

  Meas : Nat -> Bool
  Meas = \ n => (ifThenElse (isYes $ decEqUntil n f g) Omega Zero) .sequence n

  decr : Decreasing Meas
  decr n with (decEqUntil (S n) f g) proof eq
    _ | Yes eqSn = rewrite decEqUntilPred n f g (cong isYes eq) in id
    _ | No neqSn = \case prf impossible

interface IsSubSingleton x where
  isSubSingleton : (v, w : x) -> v === w

IsSubSingleton Void where
  isSubSingleton p q = absurd p

IsSubSingleton () where
  isSubSingleton () () = Refl

(IsSubSingleton a, IsSubSingleton b) => IsSubSingleton (a, b) where
  isSubSingleton (p,q) (u,v) = cong2 (,) (isSubSingleton p u) (isSubSingleton q v)

IsSubSingleton (So b) where
  isSubSingleton Oh Oh = Refl

-- K axiom
IsSubSingleton (v === w) where
  isSubSingleton Refl Refl = Refl

infix 0 ~~~
0 (~~~) : {0 b : a -> Type} -> (f, g : (x : a) ->  b x) -> Type
f ~~~ g = (x : a) -> f x === g x

0 ExtensionalEquality : Type
ExtensionalEquality
  = {0 a : Type} -> {0 b : a -> Type} ->
    {f, g : (x : a) -> b x} ->
    f ~~~ g -> f === g

interface Extensionality where
  functionalExt : ExtensionalEquality

{0 p : a -> Type} ->
  Extensionality =>
  ((x : a) -> IsSubSingleton (p x)) =>
  IsSubSingleton ((x : a) -> p x) where
  isSubSingleton v w = functionalExt (\ x => isSubSingleton (v x) (w x))

-- Extensionality is needed for the No/No case
Extensionality => IsSubSingleton p => IsSubSingleton (Dec p) where
  isSubSingleton (Yes p) (Yes q) = cong Yes (isSubSingleton p q)
  isSubSingleton (Yes p) (No nq) = absurd (nq p)
  isSubSingleton (No np) (Yes q) = absurd (np q)
  isSubSingleton (No np) (No nq) = cong No (isSubSingleton np nq)

parameters {auto _ : Extensionality}

  seqEquals : {f, g : Nat -> x} -> f ~~~ g -> f === g
  seqEquals = functionalExt

  decEqUntilSelfIsYes : Discrete x => (n : Nat) -> (f : Nat -> x) ->
                           decEqUntil n f f === Yes (\ k, bnd => Refl)
  decEqUntilSelfIsYes n f = isSubSingleton ? ?

  NatInfEquals : {f, g : Nat -> Bool} ->
                 {fdecr : Decreasing f} ->
                 {gdecr : Decreasing g} ->
                 f ~~~ g -> MkNatInf f fdecr === MkNatInf g gdecr
  NatInfEquals {f} eq with (seqEquals eq)
    _ | Refl = cong (MkNatInf f) (isSubSingleton ? ?)

  dscIsClosenessFunction : Discrete x => ClosenessFunction (Nat -> x) Tychonoff.dsc
  dscIsClosenessFunction {x}
    = MkClosenessFunction
        selfClose
        (\ v, w, eq => seqEquals (closeSelf v w eq))
        (\ v, w => NatInfEquals (symmetric v w))
        ultrametric

    where

    selfClose : (v : Nat -> x) -> dsc v v === Omega
    selfClose v = NatInfEquals $ \ n => rewrite decEqUntilSelfIsYes n v in Refl

    closeSelf : (v, w : Nat -> x) -> dsc v w === Omega -> v ~~~ w
    closeSelf v w eq n with (cong (\ f => f .sequence n) eq)
      _ | prf with (decEqUntil n v w)
        _ | Yes eqn = eqn n reflexive
        _ | No neqn = absurd prf

    symmetric : (v, w : Nat -> x) -> (dsc v w) .sequence ~~~ (dsc w v) .sequence
    symmetric v w n with (decEqUntil n v w)
      _ | Yes p with (decEqUntil n w v)
        _ | Yes q = Refl
        _ | No nq = absurd (nq $ \ k, bnd => sym (p k bnd))
      _ | No np with (decEqUntil n w v)
        _ | Yes q = absurd (np $ \ k, bnd => sym (q k bnd))
        _ | No nq = Refl

    ultrametric : (u, v, w : Nat -> x) -> min (dsc u v) (dsc v w) `LTE` dsc u w
    ultrametric u v w n with (decEqUntil n u w)
      _ | Yes r = const Oh
      _ | No nr with (decEqUntil n u v)
        _ | Yes p with (decEqUntil n v w)
          _ | Yes q = absurd (nr (\ k, bnd => trans (p k bnd) (q k bnd)))
          _ | No nq = id
        _ | No np with (decEqUntil n v w)
          _ | Yes q = id
          _ | No nq = id

closeImpliesEqUntil : Discrete x =>
  (n : Nat) -> (f, g : Nat -> x) ->
  fromNat (S n) `LTE` dsc f g ->
  EqUntil n f g
closeImpliesEqUntil n f g prf with (prf n)
  _ | prfn with (decEqUntil n f g)
    _ | Yes eqn = eqn
    _ | No neqn = absurd (prfn (soFromNat reflexive))

eqUntilImpliesClose : Discrete x =>
  (n : Nat) -> (f, g : Nat -> x) ->
  EqUntil n f g ->
  fromNat (S n) `LTE` dsc f g
eqUntilImpliesClose n f g prf k hyp with (decEqUntil k f g)
  _ | Yes p = Oh
  _ | No np = let klten = fromLteSucc $ fromNatSo {k} {n = S n} hyp in
              absurd (np $ \ k', bnd => prf k' (transitive bnd klten))

buildUp : Discrete x => (n : Nat) -> (f, g : Nat -> x) ->
  fromNat n `LTE` dsc f g ->
  (v : x) ->
  fromNat (S n) `LTE` dsc (v :: f) (v :: g)
buildUp n f g hyp v
  = eqUntilImpliesClose n (v :: f) (v :: g)
  $ \ k, bnd => case bnd of
    LTEZero => Refl
    LTESucc bnd => closeImpliesEqUntil ? f g hyp ? bnd

head : (Nat -> x) -> x
head f = f Z

tail : (Nat -> x) -> (Nat -> x)
tail f = f . S

parameters {auto _ : Extensionality}

  eta : (f : Nat -> x) -> f === head f :: tail f
  eta f = functionalExt $ \case
            Z => Refl
            S n => Refl

------------------------------------------------------------------------------
-- Continuity and continuously searchable types
------------------------------------------------------------------------------

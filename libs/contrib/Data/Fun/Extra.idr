module Data.Fun.Extra

import Data.Fun
import Data.Rel
import Data.HVect

%default total

||| Apply an n-ary function to an n-ary tuple of inputs
public export
uncurry : {0 n : Nat} -> {0 ts : Vect n Type} -> Fun ts cod -> HVect ts -> cod
uncurry f [] = f
uncurry f (x::xs) = uncurry (f x) xs

||| Apply an n-ary function to an n-ary tuple of inputs
public export
curry : {n : Nat} -> {0 ts : Vect n Type} -> (HVect ts -> cod) -> Fun ts cod
curry {ts = []    } f = f []
curry {ts = _ :: _} f = \x => curry (\xs => f (x :: xs))

{-

The higher kind Type -> Type has a monoid structure given by
composition and the identity (Cayley). The type (n : Nat ** Vect n a)
has a monoid structure given by `(n, rs) * (m, ss) := (n + m, rs +
ss)` and `(0,[])`.

  `Fun' : (n : Nat ** Vect n Type) -> Type -> Type`

is then a monoid homomorphism between them. I guess this is some
instance of Cayley's theorem, but because of extensionality we can't
show we have an isomorphism.
-}
public export
homoFunNeut_ext : Fun [] cod -> id cod
homoFunNeut_ext = id

public export
homoFunMult_ext : {n : Nat} -> {0 rs : Vect n Type} -> Fun (rs ++ ss) cod -> (Fun rs . Fun ss) cod
homoFunMult_ext {rs = []  } = id
homoFunMult_ext {rs = _::_} = (.) homoFunMult_ext

public export
homoFunNeut_inv : id cod -> Fun [] cod
homoFunNeut_inv = id

public export
homoFunMult_inv : {n : Nat} -> {0 rs : Vect n Type} -> (Fun rs . Fun ss) cod -> Fun (rs ++ ss) cod
homoFunMult_inv {rs = []  } = id
homoFunMult_inv {rs = _::_} = (.) homoFunMult_inv


||| Apply an n-ary function to an n-ary tuple of inputs
public export
applyPartially : {n : Nat} -> {0 ts : Vect n Type}
               -> Fun (ts ++ ss) cod -> (HVect ts -> Fun ss cod)
applyPartially = uncurry . homoFunMult_ext


{- -------- (slightly) dependent versions of the above ---------------
   As usual, type dependencies make everything complicated          -}

||| Apply an n-ary dependent function to its tuple of inputs (given by an HVect)
public export
uncurryAll : {0 n : Nat} -> {0 ts : Vect n Type} -> {0 cod : Fun ts Type}
        -> All ts cod -> (xs : HVect ts) -> uncurry cod xs
uncurryAll f [] = f
uncurryAll f (x :: xs) = uncurryAll (f x) xs

public export
curryAll : {n : Nat} -> {0 ts : Vect n Type} -> {0 cod : Fun ts Type}
        -> ((xs : HVect ts) -> uncurry cod xs)
        -> All ts cod
curryAll {ts = []  } f = f []
curryAll {ts = _::_} f = \x => curryAll (\xs => f (x :: xs))

chainGenUncurried : {n : Nat} -> {0 ts : Vect n Type} -> {0 cod,cod' : Fun ts Type} ->
           ((xs : HVect ts) -> uncurry cod xs -> uncurry cod' xs) ->
           All ts cod -> All ts cod'
chainGenUncurried {ts = []  } f gs = f [] gs
chainGenUncurried {ts = _::_} f gs = \x => chainGenUncurried (\u => f (x :: u)) (gs x)

public export
homoAllNeut_ext : Fun [] cod -> id cod
homoAllNeut_ext = id

-- Not sure it's worth it getting the rest of Cayley's theorem to work

public export
extractWitness : {n : Nat} -> {0 ts : Vect n Type} -> {0 r : Rel ts} -> Ex ts r -> HVect ts
extractWitness {ts = []  }  _       = []
extractWitness {ts = _::_} (w ** f) = w :: extractWitness f

public export
extractWitnessCorrect : {n : Nat} -> {0 ts : Vect n Type} -> {0 r : Rel ts} -> (f : Ex ts r) ->
                        uncurry {ts} r (extractWitness {r} f)
extractWitnessCorrect {ts = []  } f = f
extractWitnessCorrect {ts = _::_} (w ** f) = extractWitnessCorrect f

public export
introduceWitness : {0 r : Rel ts} -> (witness : HVect ts) ->
                   uncurry {ts} r witness -> Ex ts r
introduceWitness []             f = f
introduceWitness (w :: witness) f = (w ** introduceWitness witness f)

----------------------------------------------------------------------
public export
data Pointwise : (r : a -> b -> Type) -> (ts : Vect n a) -> (ss : Vect n b) -> Type where
  Nil  : Pointwise r [] []
  (::) : {0 ss, ts : Vect n Type} ->
         (f : r t s) -> Pointwise r ts ss -> Pointwise r (t::ts) (s::ss)

public export
precompose : Pointwise (\a,b => a -> b) ts ss -> Fun ss cod -> Fun ts cod
precompose [] h = h
precompose (f :: fs) h = precompose fs . h . f

||| Uncurrying a Fun and then composing with a normal function
||| is extensionally equal to
||| composing functions using `chain`, then uncurrying.
public export
chainUncurry :
  {0 ts : Vect n Type}
  -> (g : Fun ts r)
  -> (f : r -> r')
  -> (elems : HVect ts)
  -> f (uncurry g elems)  = uncurry (chain {ts} f g) elems
chainUncurry g f []   =  Refl
chainUncurry g f (x :: xs)  = rewrite chainUncurry (g x) f xs in Refl

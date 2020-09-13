module Data.Fun.Extra

import Data.Fun
import Data.HVect

||| Apply an n-ary function to an n-ary tuple of inputs
public export
apply : {ts : Vect n Type} -> {cod : Type} -> Fun ts cod -> HVect ts -> cod
apply f [] = f
apply f (t::ts) = apply (f t) ts

||| Apply an n-ary function to an n-ary tuple of inputs
public export
applyPartially : {ts : Vect n Type} -> {ss : Vect m Type} -> {rs : Vect k Type} 
               -> {auto 0 fordShape : rs = ts ++ ss}
               -> {cod : Type} -> Fun rs cod -> HVect ts -> Fun ss cod
applyPartially {fordShape = Refl} f [] = f
applyPartially {fordShape = Refl} f (x::xs) = applyPartially (f x) xs


{- -------- (slightly) dependent versions of the above ---------------
   As usual, type dependencies make everything complicated          -}


||| Build an n-ary dependent function type from a Vect of Types and a dependent result type
||| NB: the types in the tuple do not depend on each other.
public export
GenFun : (ts : Vect n Type) -> (cod : Fun ts Type) -> Type
GenFun [] cod = cod
GenFun (t :: ts) cod = (x : t) -> GenFun ts (cod x )

||| Apply an n-ary dependent function to its tuple of inputs (given by an HVect)
public export
applyGen : {ts : Vect n Type} -> {cod : Fun ts Type} 
        -> GenFun ts cod -> (xs : HVect ts) -> apply cod xs
applyGen f [] = f
applyGen {ts = t :: ts} {cod} f (x :: xs) = applyGen {cod= cod x} (f x) xs

chainGenUncurried : {ts : Vect n Type} -> {cod,cod' : Fun ts Type} -> 
           ((xs : HVect ts) -> apply cod xs -> apply cod' xs) ->  
           GenFun ts cod -> GenFun ts cod'
chainGenUncurried {ts = []} f gs = f [] gs
chainGenUncurried {ts = (t :: ts)} f gs = \x => chainGenUncurried (\u => f (x :: u)) (gs x)

||| Partially apply an n-ary dependent function to a tuple of its inputs
||| Yes, the type is disgusting
applyPartiallyGen : {ts : Vect n Type} -> {ss : Vect m Type} -> {rs : Vect k Type} 
                -> {cod : Fun rs Type} 
                -> {auto 0 fordShape : rs = ts ++ ss}
                -> GenFun rs cod -> (xs : HVect ts) -> 
                   GenFun ss $ applyPartially {ts} {ss} {rs} {cod = Type} cod xs
applyPartiallyGen {ts = []     } {fordShape = Refl} f [] = f
applyPartiallyGen {ts = t :: ts} {fordShape = Refl} f (x :: xs) = applyPartiallyGen (f x) xs
  

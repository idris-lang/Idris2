||| Contains:
|||
||| 1. Tail recursive versions of the list processing functions from
|||    Data.List.
|||
||| 2. Extensional equality proofs that these variants are
|||    (extensionally) equivalent to their non-tail-recursive
|||    counterparts.
|||
||| Note:
|||
||| 1. Written in one sitting, feel free to refactor
|||
||| 2. The proofs below also work on non-publicly exported
|||    definitions.  This could be due to a bug, and will need to be
|||    moved elsewhere if it's fixed.
module Data.List.TailRec

import Syntax.PreorderReasoning
import Syntax.WithProof

import Data.List
import Data.List1
import Data.Vect
import Data.Nat

total
lengthAcc : List a -> Nat -> Nat
lengthAcc [] acc = acc
lengthAcc (_::xs) acc = lengthAcc xs $ S acc

export total
length : List a -> Nat
length xs = lengthAcc xs Z

total
lengthAccSucc : (xs : List a) -> (n : Nat) -> lengthAcc xs (S n) = S (lengthAcc xs n)
lengthAccSucc [] _ = Refl
lengthAccSucc (_::xs) n = rewrite lengthAccSucc xs (S n) in cong S Refl

export total
length_ext : (xs : List a) -> List.length xs = Data.List.TailRec.length xs
length_ext [] = Refl
length_ext (_::xs) = rewrite length_ext xs in sym $ lengthAccSucc xs Z

take_aux : Nat -> List a -> List a -> List a
take_aux Z     xs        acc = reverseOnto [] acc
take_aux (S n) []        acc = reverseOnto [] acc
take_aux (S n) (x :: xs) acc = take_aux n xs (x :: acc)

export
take : Nat -> List a -> List a
take n xs = take_aux n xs []

export
take_ext :
  (n : Nat) -> (xs : List a) ->
     Data.List.take n xs = Data.List.TailRec.take n xs
take_ext n xs = Calc $
  |~ Data.List.take n xs
  ~~ reverse [] ++ (Data.List.take n xs)  ...( Refl )
  ~~ reverseOnto (Data.List.take n xs) [] ...( sym (revOnto (Data.List.take n xs) []) )
  ~~ take_aux n xs []                     ...( sym (lemma n xs []) )
  where
    lemma : (n : Nat) -> (xs, acc : List a) ->
            take_aux n xs acc =  reverseOnto (Data.List.take n xs) acc
    lemma Z     xs      acc = Refl
    lemma (S n) []      acc = Refl
    lemma (S n) (x::xs) acc = lemma n xs (x :: acc)


span_aux : (a -> Bool) -> List a -> List a -> (List a, List a)
span_aux p []      acc = (reverseOnto [] acc, [])
span_aux p (x::xs) acc =
  if p x then
    Data.List.TailRec.span_aux p xs (x :: acc)
  else
    (reverseOnto [] acc, x::xs)

export
span : (a -> Bool) -> List a -> (List a, List a)
span p xs = span_aux p xs []

coe : (f : (i : a) -> Type) -> i = i' -> f i -> f i'
coe f Refl x = x

span_aux_ext : (p : a -> Bool) -> (xs, acc : List a) ->
  (reverseOnto (fst $ Data.List.span p xs) acc, snd $ Data.List.span p xs)
  =
  span_aux p xs acc
span_aux_ext p []      acc = Refl
-- This is disgusting. Please teach me a better way.
span_aux_ext p (x::xs) acc with (@@(p x), @@(Data.List.span p xs))
 span_aux_ext p (x::xs) acc | ((True ** px_tru), ((pre, rest)**dl_pf)) =
   rewrite px_tru in
   rewrite dl_pf in
   let u = span_aux_ext p xs (x::acc) in
   coe (\u => (reverseOnto (x :: fst u) acc, snd u) =
               Data.List.TailRec.span_aux p xs (x :: acc)) dl_pf u
 span_aux_ext p (x::xs) acc | ((False**px_fls), ((pre,rest)**dl_pf)) =
   rewrite px_fls in
   Refl

export
span_ext : (p : a -> Bool) -> (xs : List a) ->
  Data.List.span p xs = Data.List.TailRec.span p xs
span_ext p xs with (@@(Data.List.span p xs))
  span_ext p xs |  ((pre, rest) ** pf) =
    rewrite pf in
    let u = span_aux_ext p xs [] in
    coe (\u => (fst u, snd u) = span_aux p xs []) pf u

export
break : (a -> Bool) -> List a -> (List a, List a)
break p xs = Data.List.TailRec.span (not . p) xs

export
break_ext : (p : a -> Bool) -> (xs : List a) ->
  Data.List.break p xs = Data.List.TailRec.break p xs
break_ext p xs = span_ext (not . p) xs

splitOnto : List (List a) -> (a -> Bool) -> List a -> List1 (List a)
splitOnto acc p xs =
  case Data.List.break p xs of
    (chunk, []       ) => reverseOnto (chunk ::: []) acc
    (chunk, (c::rest)) => splitOnto (chunk::acc) p rest

export
split : (a -> Bool) -> List a -> List1 (List a)
split p xs = splitOnto [] p xs

splitOnto_ext : (acc : List (List a)) -> (p : a -> Bool) -> (xs : List a) ->
              reverseOnto (Data.List.split p xs) acc
              = Data.List.TailRec.splitOnto acc p xs
splitOnto_ext  acc p xs with (@@(Data.List.break p xs))
 splitOnto_ext acc p xs | ((chunk,  []    )**pf) =
   rewrite pf in
   Refl
 splitOnto_ext acc p xs | ((chunk, c::rest)**pf) =
   rewrite pf in
   rewrite splitOnto_ext (chunk::acc) p rest in
   Refl

export
split_ext : (p : a -> Bool) -> (xs : List a) ->
  Data.List.split p xs = Data.List.TailRec.split p xs
split_ext p xs = splitOnto_ext [] p xs


splitAtOnto : List a -> (n : Nat) -> (xs : List a) -> (List a, List a)
splitAtOnto acc Z     xs      = (reverseOnto [] acc, xs)
splitAtOnto acc (S n) []      = (reverseOnto [] acc, [])
splitAtOnto acc (S n) (x::xs) = splitAtOnto (x::acc) n xs

export
splitAt : (n : Nat) -> (xs : List a) -> (List a, List a)
splitAt n xs = splitAtOnto [] n xs

splitAtOnto_ext : (acc : List a) -> (n : Nat) -> (xs : List a) ->
  (reverseOnto (fst $ Data.List.splitAt n xs) acc, snd $ Data.List.splitAt n xs)
  = splitAtOnto acc n xs
splitAtOnto_ext  acc Z     xs      = Refl
splitAtOnto_ext  acc (S n) []      = Refl
splitAtOnto_ext  acc (S n) (x::xs) with (@@(Data.List.splitAt n xs))
 splitAtOnto_ext acc (S n) (x::xs) | ((tk, dr)**pf) =
   rewrite pf in
   let u = splitAtOnto_ext (x::acc) n xs in
   coe (\u => (reverseOnto (x :: fst u) acc, snd u) =
                      splitAtOnto (x :: acc) n xs) pf u

export
splitAt_ext : (n : Nat) -> (xs : List a) ->
  Data.List.splitAt n xs =
  Data.List.TailRec.splitAt n xs
splitAt_ext  n xs with (@@(Data.List.splitAt n xs))
 splitAt_ext n xs | ((tk, dr)**pf) =
   rewrite pf in
   rewrite sym $ splitAtOnto_ext [] n xs in
   rewrite pf in
   Refl

partitionOnto : List a -> List a -> (a -> Bool) -> List a -> (List a, List a)
partitionOnto lfts rgts p []      = (reverseOnto [] lfts, reverseOnto [] rgts)
partitionOnto lfts rgts p (x::xs) =
  if p x then
    partitionOnto (x :: lfts)     rgts  p xs
  else
    partitionOnto       lfts  (x::rgts) p xs

export
partition : (a -> Bool) -> List a -> (List a, List a)
partition p xs = partitionOnto [] [] p xs

partitionOnto_ext : (lfts, rgts : List a) -> (p : a -> Bool) -> (xs : List a) ->
  (reverseOnto (fst $ Data.List.partition p xs) lfts
  ,reverseOnto (snd $ Data.List.partition p xs) rgts)
  = Data.List.TailRec.partitionOnto lfts rgts p xs
partitionOnto_ext  lfts rgts p [] = Refl
partitionOnto_ext  lfts rgts p (x::xs) with (@@(p x), @@(Data.List.partition p xs))
 partitionOnto_ext lfts rgts p (x::xs) | ((True **px_tru), ((dl_l, dl_r)**dl_pf))
   = rewrite px_tru in
     rewrite dl_pf  in
     rewrite px_tru in
     let u = partitionOnto_ext (x :: lfts) rgts p xs in
     coe (\u => (reverseOnto (x :: fst u) lfts
                ,reverseOnto (     snd u) rgts)
                = partitionOnto (x :: lfts) rgts p xs) dl_pf u

 partitionOnto_ext lfts rgts p (x::xs) | ((False**px_fls), ((dl_l, dl_r)**dl_pf))
   = rewrite px_fls in
     rewrite dl_pf  in
     rewrite px_fls in
     let u = partitionOnto_ext lfts (x :: rgts) p xs in
     coe (\u => (reverseOnto (     fst u) lfts
                ,reverseOnto (x :: snd u) rgts)
                = partitionOnto lfts (x::rgts) p xs) dl_pf u

mergeReplicate_aux : a -> List a -> List a -> List a
mergeReplicate_aux sep []      acc = reverseOnto [] acc
mergeReplicate_aux sep (x::xs) acc = mergeReplicate_aux sep xs (x :: sep :: acc)

mergeReplicate_ext : (sep : a) -> (xs : List a) -> (acc : List a) ->
                   mergeReplicate_aux sep xs acc =
                   reverseOnto (mergeReplicate sep xs) acc
mergeReplicate_ext sep []      acc = Refl
mergeReplicate_ext sep (x::xs) acc = Calc $
  |~ mergeReplicate_aux sep xs (x :: sep :: acc)
  ~~ reverseOnto (sep :: x :: mergeReplicate sep xs) acc
                              ...( mergeReplicate_ext sep xs (x :: sep :: acc) )

export
intersperse : a -> List a -> List a
intersperse sep []      = []
intersperse sep (y::ys) = y :: mergeReplicate_aux sep ys []

export
intersperse_ext : (sep : a) -> (xs : List a) ->
              Data.List.intersperse sep xs =
              Data.List.TailRec.intersperse sep xs
intersperse_ext sep [] = Refl
intersperse_ext sep (y::ys) = cong (y::) (sym $ mergeReplicate_ext sep ys [])

mapMaybeOnto : List b -> (a -> Maybe b) -> List a -> List b
mapMaybeOnto acc f [] = reverseOnto [] acc
mapMaybeOnto acc f (x::xs) =
  case f x of
    Nothing => mapMaybeOnto acc f xs
    Just  y => mapMaybeOnto (y :: acc) f xs

export
mapMaybe : (a -> Maybe b) -> List a -> List b
mapMaybe f xs = mapMaybeOnto [] f xs

mapMaybeOnto_ext : (acc : List b) -> (f : a -> Maybe b) -> (xs : List a) ->
  reverseOnto (Data.List.mapMaybe f xs) acc
  =
  mapMaybeOnto acc f xs
mapMaybeOnto_ext  acc f []                = Refl
mapMaybeOnto_ext  acc f (x::xs) with (f x)
 mapMaybeOnto_ext acc f (x::xs) | Nothing = mapMaybeOnto_ext acc f xs
 mapMaybeOnto_ext acc f (x::xs) | Just  y = mapMaybeOnto_ext (y :: acc) f xs

export
mapMaybe_ext : (f : a -> Maybe b) -> (xs : List a) ->
  Data.List.mapMaybe f xs = Data.List.TailRec.mapMaybe f xs
mapMaybe_ext f xs = mapMaybeOnto_ext [] f xs

export
sorted : Ord a => List a -> Bool
sorted [ ] = True
sorted [x] = True
sorted  (x :: xs@(y :: ys)) = case (x <= y) of
                                False => False
                                True  => Data.List.TailRec.sorted xs

export
sorted_ext : Ord a => (xs : List a) ->
  Data.List.sorted xs = Data.List.TailRec.sorted xs
sorted_ext []  = Refl
sorted_ext [x] = Refl
sorted_ext  (x :: y :: ys) with (x <= y)
 sorted_ext (x :: y :: ys) | False = Refl
 sorted_ext (x :: y :: ys) | True  = sorted_ext (y::ys)

mergeByOnto : List a -> (a -> a -> Ordering) -> List a -> List a -> List a
mergeByOnto acc order []           right         = reverseOnto right acc
mergeByOnto acc order left         []            = reverseOnto left  acc
mergeByOnto acc order left@(x::xs) right@(y::ys) =
  -- We need the variant annotations (bug #300)
  case order x y of
    LT => mergeByOnto (x :: acc) order (assert_smaller left xs)   right
    _  => mergeByOnto (y :: acc) order left                       (assert_smaller right ys)

mergeByOnto_ext : (acc : List a)
               -> (order : a -> a -> Ordering)
               -> (left, right : List a)
               -> reverseOnto (mergeBy order left right) acc
                  = mergeByOnto acc order left right
mergeByOnto_ext acc order []           right         = Refl
mergeByOnto_ext  acc order left        []            with( left)
 mergeByOnto_ext acc order _           []            | []     = Refl
 mergeByOnto_ext acc order _           []            | (_::_) = Refl
mergeByOnto_ext acc order left@(x::xs) right@(y::ys) with (order x y)
 mergeByOnto_ext acc order left@(x::xs) right@(y::ys) | LT =
                           mergeByOnto_ext (x :: acc) order xs (y::ys)
 -- We need to exhaust the two other cases explicitly to convince the
 -- typecheker. See #140
 mergeByOnto_ext acc order left@(x::xs) right@(y::ys) | EQ =
                           mergeByOnto_ext (y :: acc) order (x::xs) ys
 mergeByOnto_ext acc order left@(x::xs) right@(y::ys) | GT =
                           mergeByOnto_ext (y :: acc) order (x::xs) ys

export
mergeBy : (a -> a -> Ordering) -> List a -> List a -> List a
mergeBy order left right = mergeByOnto [] order left right

export
mergeBy_ext : (order : a -> a -> Ordering) -> (left, right : List a) ->
  Data.List.mergeBy order left right =
  Data.List.TailRec.mergeBy order left right
mergeBy_ext order left right = mergeByOnto_ext [] order left right

export
merge : Ord a => List a -> List a -> List a
merge = Data.List.TailRec.mergeBy compare

export
merge_ext : Ord a => (left, right : List a) ->
  Data.List.merge left right = Data.List.TailRec.merge left right
merge_ext left right = mergeBy_ext compare left right


-- Not quite finished due to a bug.

sortBy_splitRec : List a -> List a -> (List a -> List a) -> (List a, List a)
sortBy_splitRec (_::_::xs) (y::ys) zs = sortBy_splitRec xs ys (zs . ((::) y))
sortBy_splitRec _          ys      zs = (zs [], ys)

sortBy_split : List a -> (List a, List a)
sortBy_split xs = sortBy_splitRec xs xs id

export
sortBy : (cmp : a -> a -> Ordering) -> (xs : List a) -> List a
sortBy cmp []  = []
sortBy cmp [x] = [x]
sortBy cmp zs = let (xs, ys) = sortBy_split zs in
    Data.List.TailRec.mergeBy cmp
          (Data.List.TailRec.sortBy cmp (assert_smaller zs xs))
          (Data.List.TailRec.sortBy cmp (assert_smaller zs ys))


 {- Can't really finish this proof because Data.List doesn't export the definition of sortBy. -}
 {-
export
sortBy_ext : (cmp : a -> a -> Ordering) -> (xs : List a) ->
  Data.List.sortBy cmp xs = Data.List.TailRec.sortBy cmp xs
sortBy_ext  cmp []  = Refl
sortBy_ext  cmp [x] = Refl
sortBy_ext  cmp zs'@(z::zs) =
  Calc $
  |~ Data.List.sortBy cmp (z::zs)
  ~~ (let (xs, ys) = sortBy_split zs' in
     Data.List.mergeBy cmp
     (Data.List.sortBy cmp xs)
     (Data.List.sortBy cmp ys))
      ...( ?help0 )
  ~~
  let (xs, ys) = sortBy_split (z::zs) in
  Data.List.TailRec.mergeBy cmp
    (Data.List.TailRec.sortBy cmp xs)
    (Data.List.TailRec.sortBy cmp ys)
    ...( ?help1 )
-}

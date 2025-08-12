module Libraries.Data.NatSet

import Data.Bits
import Data.List
import Data.SnocList
import Libraries.Data.SnocList.Extra

%default total

export
NatSet : Type
NatSet = Integer

export %inline
empty : NatSet
empty = 0

export %inline
elem : Nat -> NatSet -> Bool
elem = flip testBit

export
drop : NatSet -> List a -> List a
drop 0  xs = xs
drop ds xs = go 0 xs
  where
    go : Nat -> List a -> List a
    go _ [] = []
    go i (x :: xs)
        = if i `elem` ds
             then go (S i) xs
             else x :: go (S i) xs

export %inline
take : NatSet -> List a -> List a
take = drop . complement

export
isEmpty : NatSet -> Bool
isEmpty 0 = True
isEmpty _ = False

export
size : NatSet -> Nat
size = go 0
  where
    go : Nat -> NatSet -> Nat
    go acc 0 = acc
    go acc n =
      -- cast is modulo, i.e. takes the lower bits
      let acc = acc + popCount (the Int64 (cast n)) in
      go acc (assert_smaller n (shiftR n 64))

export %inline
Cast NatSet Integer where
  cast ns = ns

export %inline
Cast Integer NatSet where
  cast n = n

export
insert : Nat -> NatSet -> NatSet
insert = flip setBit

export
delete : Nat -> NatSet -> NatSet
delete = flip clearBit

export
toList : NatSet -> List Nat
toList = go 0
  where
    go : Nat -> NatSet -> List Nat
    go i 0 = []
    go i ns =
       let is = go (S i) (assert_smaller ns (shiftR ns 1)) in
       if 0 `elem` ns then i :: is else is

fromList : List Nat -> NatSet
fromList = foldr insert empty

export
Show NatSet where
  show ns = show (toList ns)

export
partition : NatSet -> List a -> (List a , List a)
partition ps = go 0
  where
    go : Nat -> List a -> (List a , List a)
    go i [] = ([], [])
    go i (x :: xs)
      = let xys = go (S i) xs in
        if i `elem` ps
           then mapFst (x ::) xys
           else mapSnd (x ::) xys

export
intersection : NatSet -> NatSet -> NatSet
intersection = (.&.)

export
union : NatSet -> NatSet -> NatSet
union = (.|.)

export
intersectAll : List NatSet -> NatSet
intersectAll [] = empty
intersectAll (x::xs) = foldr intersection x xs

export
allLessThan : Nat -> NatSet
allLessThan n = shiftL 1 n - 1

0 allLessThanSpecEmpty : toList (allLessThan 0) === []
allLessThanSpecEmpty = Refl

0 allLessThanSpecNonEmpty : toList (allLessThan 10) === [0..9]
allLessThanSpecNonEmpty = Refl

export
overwrite : a -> NatSet -> List a -> List a
overwrite c 0  xs = xs
overwrite c ds xs = go 0 xs
  where
    go : Nat -> List a -> List a
    go _ [] = []
    go i (x :: xs)
        = if i `elem` ds
             then c :: go (S i) xs
             else x :: go (S i) xs



-- Pop the zero (whether or not in the set) and shift all the
-- other positions by -1 (useful when coming back from under
-- a binder)
export %inline
popZ : NatSet -> NatSet
popZ = (`shiftR` 1)

export %inline
popNs : Nat -> NatSet -> NatSet
popNs = flip shiftR

-- Add a 'new' Zero (not in the set) and shift all the
-- other positions by +1 (useful when going under a binder)
export %inline
addZ : NatSet -> NatSet
addZ = (`shiftL` 1)

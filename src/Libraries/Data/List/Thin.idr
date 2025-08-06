module Libraries.Data.List.Thin

import Libraries.Data.NatSet

%default total

-- TODO implement:
-- Guillaume Allais: Builtin Types Viewed as Inductive Families
-- https://doi.org/10.48550/arXiv.2301.02194
public export
data Thin : List a -> List a -> Type where
  Refl : Thin xs xs
  Drop : Thin xs ys -> Thin xs (y :: ys)
  Keep : Thin xs ys -> Thin (x :: xs) (x :: ys)

export
none : {xs : List a} -> Thin [] xs
none {xs = []} = Refl
none {xs = _ :: _} = Drop none

||| Smart constructor. We should use this to maximise the length
||| of the Refl segment thus getting more short-circuiting behaviours
export
keep : Thin xs ys -> Thin (x :: xs) (x :: ys)
keep Refl = Refl
keep p = Keep p

export
keeps : (args : List a) -> Thin xs ys -> Thin (args ++ xs) (args ++ ys)
keeps [] th = th
keeps (x :: xs) th = Keep (keeps xs th)

export
fromNatSet : NatSet -> (xs : List a) -> (xs' ** Thin xs' xs)
fromNatSet ns xs =
  if isEmpty ns then (_ ** Refl) else go 0 xs
  where
    go : Nat -> (xs : List a) -> (xs' ** Thin xs' xs)
    go i [] = (_ ** Refl)
    go i (x :: xs)
        = let (xs' ** th) = go (S i) xs in
              if i `elem` ns
                 then (xs' ** Drop th)
                 else (x :: xs' ** Keep th)

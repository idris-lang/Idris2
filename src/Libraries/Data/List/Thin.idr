module Libraries.Data.List.Thin

import Libraries.Data.NatSet
import Libraries.Data.SnocList.SizeOf

%default total

public export
data Thin : SnocList a -> SnocList a -> Type where
  Refl : Thin xs xs
  Drop : Thin xs ys -> Thin xs (ys :< y)
  Keep : Thin xs ys -> Thin (xs :< x) (ys :< x)

-- At runtime, Thin's `Refl` does not carry any additional
-- information. So this is safe!
export
embed : Thin xs ys -> Thin (outer ++ xs) (outer ++ ys)
embed = believe_me

export
none : {xs : SnocList a} -> Thin [<] xs
none {xs = [<]} = Refl
none {xs = _ :< _} = Drop none

||| Smart constructor. We should use this to maximise the length
||| of the Refl segment thus getting more short-circuiting behaviours
export
keep : Thin xs ys -> Thin (xs :< x) (ys :< x)
keep Refl = Refl
keep p = Keep p

export
keeps : (args : SnocList a) -> Thin xs ys -> Thin (xs ++ args) (ys ++ args)
keeps [<] th = th
keeps (sx :< x) th = Keep (keeps sx th)

export
keepz : (args : List a) -> Thin xs ys -> Thin (xs <>< args) (ys <>< args)
keepz [] th = th
keepz (x :: xs) th = keepz xs (keep th)

export
fromNatSet : NatSet -> (xs : SnocList a) -> (xs' ** Thin xs' xs)
fromNatSet ns xs =
  if isEmpty ns then (_ ** Refl) else go xs (mkSizeOf xs)
  where
    go : (xs : SnocList a) -> SizeOf xs -> (xs' ** Thin xs' xs)
    go l s with (sizedView s)
      go _ _ | Z = (_ ** Refl)
      go (xs :< x) _ | (S s@(MkSizeOf i _))
        = let (xs' ** th) = go xs s in
              if i `elem` ns
                 then (xs' ** Drop th)
                 else (xs' :< x ** Keep th)

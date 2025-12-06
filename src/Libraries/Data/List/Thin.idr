module Libraries.Data.List.Thin

import Libraries.Data.NatSet

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
  if isEmpty ns then (_ ** Refl) else go (length xs) xs
  where
    go : Nat -> (xs : SnocList a) -> (xs' ** Thin xs' xs)
    go i [<] = (_ ** Refl)
    go (S i) (xs :< x)
        = let (xs' ** th) = go i xs in
              if i `elem` ns
                 then (xs' ** Drop th)
                 else (xs' :< x ** Keep th)
    -- Next case can't happen if called with the right Nat from fromNatSet
    -- FIXME: rule it out with a type!
    -- Dupe see: Compiler.CompileExpr.mkDropSubst
    -- Dupe see: Libraries.Data.NatSet.drop
    go Z (xs :< x) = let (xs' ** th) = go Z xs in (xs' ** Drop th)

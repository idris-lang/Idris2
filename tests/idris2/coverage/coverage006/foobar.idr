foo : (pf : Nat -> Either (S Z = Z) (Z = S Z)) -> Z = S Z
foo  pf =
 let baz : Z === S Z
     baz  with (pf 0)
      baz | (Left Refl) impossible
      baz | (Right pf') = pf'
 in baz

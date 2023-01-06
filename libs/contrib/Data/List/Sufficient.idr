||| 'Sufficient' lists: a structurally inductive view of lists xs
||| as given by xs = non-empty prefix + sufficient suffix
|||
||| Useful for termination arguments for function definitions
||| which provably consume a non-empty (but otherwise arbitrary) prefix
||| *without* having to resort to ancillary WF induction on length etc.
||| e.g. lexers, parsers etc.
|||
||| Credited by Conor McBride as originally due to James McKinna
module Data.List.Sufficient

||| Sufficient view
public export
data Sufficient : (xs : List a) -> Type where
  SuffAcc : {xs : List a}
          -> (suff_ih : {x : a} -> {pre, suff : List a}
                      -> xs = x :: (pre ++ suff)
                      -> Sufficient suff)
          -> Sufficient xs

||| Sufficient view covering property
export
sufficient : (xs : List a) -> Sufficient xs
sufficient []        = SuffAcc (\case _ impossible)
sufficient (x :: xs) with (sufficient xs)
  sufficient (x :: xs) | suffxs@(SuffAcc suff_ih)
    = SuffAcc (\case Refl => prf Refl)
    where prf : {pre, suff : List a}
              -> xs = pre ++ suff
              -> Sufficient suff
          prf {pre = []} Refl = suffxs
          prf {pre = (y :: ys)} eq = suff_ih eq

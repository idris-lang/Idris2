transport : (0 eq : a === b) -> a -> b
transport eq x = rewrite sym eq in x

nested : (0 _ : a === b) -> (0 _ : b === c) -> a === c
nested eq1 eq2 =
  rewrite eq1 in
    rewrite eq2 in
      let prf : c === c := Refl in
      prf

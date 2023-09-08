data Foobar : String -> Type where
  MkBar : (s : String) -> Foobar s

test : (foobar : (x ** Foobar x)) -> String
test (MkDPair fst snd) with (snd)
  test (MkDPair fst snd) | (MkBar fst) = ?test_rhs__rhs_

test' : (foobar : (x ** Foobar x)) -> String
test' (s ** foobar) with (foobar)
  test' (s ** foobar) | with_pat = ?test'_rhs_rhs

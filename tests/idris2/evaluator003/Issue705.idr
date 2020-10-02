-- %logging compile.casetree 5
-- %logging eval.casetree 5

-- %logging declare.def.lhs 5

bad : (a : Type) -> (x : a) -> String
bad String "good" = "good"
bad (List Nat) [1,2] = "good"
bad Char 'c' = "good"
bad _ _ = "bad"

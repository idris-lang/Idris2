mutual
  caseTest : Nat -> Bool
  caseTest p with (dummy)
   caseTest p | _ = True

  dummy : Nat
  dummy = case (caseTest 0) of
             True => 0
             _ => 0

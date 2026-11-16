module WithMulti

%default total

-- Previously, `arg` was captured, in one of the recursive calls,
-- leading to a type mismatch.
capture : Nat -> Nat -> Maybe Nat
capture arg (S n) with (capture arg n) | (capture arg n)
  _ | Just  l | Just  r = Just (l + r)
  _ | Nothing | Just  r = Just r
  _ | Just  l | Nothing = Just l
  _ | Nothing | Nothing = Nothing
capture arg Z = Just 1

decEq : (s, s' : String) -> Dec (s = s')
decEq s s' = ?dec

-- Test cases from issue 3529
symmetric : (s, s' : String) -> (s == s') = (s' == s)
symmetric s s' with (decEq s s') proof f | (s == s') | (s' == s)
  symmetric s s' | (No  ne) | False | e = ?rhs0
  symmetric s s' | (No  ne) | True  | e = ?rhs1
  symmetric s s' | (Yes ye) | True  | e = ?rhs2
  symmetric s s' | (Yes ye) | False | e = ?rhs3

symmetric' : (s, s' : String) -> (s == s') = (s' == s)
symmetric' s s'
  with (s == s') proof e
     | (s' == s) proof e'
     | (decEq s s') proof de
     | (decEq s' s) proof de'
  _ | False | False | _ | _ = Refl
  _ | True  | True  | _ | _ = Refl
  _ | False | True  | Yes eq | Yes eq' = ?rhs4
  _ | False | True  | Yes eq | No neq' = absurd . neq' $ sym eq
  _ | False | True  | No neq | Yes eq' = absurd . neq $ sym eq'
  _ | False | True  | No neq | No neq' = ?rhs6
  _ | True  | False | Yes eq | Yes eq' = ?rhs7
  _ | True  | False | Yes eq | No neq' = absurd . neq' $ sym eq
  _ | True  | False | No neq | Yes eq' = absurd . neq $ sym eq'
  _ | True  | False | No neq | No neq' = ?rhs10

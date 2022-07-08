interface TFEq (0 c : Type -> Type) where
  tfEq : c v1 -> c v2 -> Bool

test : c v1 -> c v2 -> TFEq c => Int
test c1 c2 = let v = tfEq c1 c2
             in if v then 1 else 0

test1 : c v1 -> c v2 -> TFEq c => Int
test1 c1 c2 = if tfEq {v1=v1} {v2=v2} c1 c2 then 1 else 0

test2 : c v1 -> c v2 -> TFEq c => Bool
test2 c1 c2 = tfEq c1 c2

test3 : c v1 -> c v2 -> TFEq c => Int
test3 c1 c2 = case tfEq c1 c2 of
   True => 1
   False => 0

test4 : c v1 -> c v2 -> TFEq c => Int
test4 c1 c2 = if tfEq c1 c2 then 1 else 0

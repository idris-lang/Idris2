data Bar = MkBar
data Baz = MkBaz

strangeId : a -> a
strangeId {a=Nat} x = x+1
strangeId x = x

foo : (0 x : Type) -> String
foo Nat = "Nat"
foo Bool = "Bool"
foo (List x) = "List of " ++ foo x
foo Int = "Int"
foo Type = "Type"
foo _ = "Something else"

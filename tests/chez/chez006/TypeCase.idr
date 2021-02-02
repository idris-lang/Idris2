data Bar = MkBar
data Baz = MkBaz

foo : (x : Type) -> String
foo Nat = "Nat"
foo Bool = "Bool"
foo (List x) = "List of " ++ foo x
foo Int = "Int"
foo Type = "Type"
foo _ = "Something else"

strangeId : {a : Type} -> a -> a
strangeId {a=Integer} x = x+1
strangeId x = x

partial
strangeId' : {a : Type} -> a -> a
strangeId' {a=Integer} x = x+1

main : IO ()
main = do printLn (foo Nat)
          printLn (foo (List Nat))
          printLn (foo (List Bar))
          printLn (foo (List Baz))
          printLn (foo (List Bool))
          printLn (foo Int)
          printLn (foo String)
          printLn (foo (List Type))
          printLn (foo (List Int))
          printLn (strangeId 42)
          printLn (strangeId (the Int 42))

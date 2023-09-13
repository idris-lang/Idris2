module NoDeclaration

identity : (a : Type) -> a -> a
identity _ x = x

idNat = identity Nat

double = (S 1 *)

test : idNat (double 3) === 6
test = Refl

unwords : List String -> String
unwords [] = ""
unwords [x] = x
unwords (x::xs) = x ++ " " ++ unwords xs

helloWorld = unwords ["hello", "world"]

test' : NoDeclaration.helloWorld === "hello world"
test' = Refl

cat x y = unwords [x, show {ty = Nat} y]

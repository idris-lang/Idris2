-- https://github.com/idris-lang/Idris2/issues/1282#issue-852601557
0 Alias : Type -> Type
Alias a = (b : Bool) -> if b then a else a
foo : Alias ()
foo = ?test1

-- https://github.com/idris-lang/Idris2/issues/2461#issue-1228334999
test2 = \x => (\y => the Bool $ if y then y else y) x

test_fold = \a, b, c => foldl (\acc, i => case i of Z => S acc; _ => acc) Z [a, b, c]

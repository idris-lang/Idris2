module PrimLoop

%default total

loop : Nat -> PrimIO ()
loop Z     w = MkIORes () w
loop (S k) w =
  let MkIORes () w2 := toPrim (printLn (S k)) w
   in loop k w2

main : IO ()
main = fromPrim $ loop 10

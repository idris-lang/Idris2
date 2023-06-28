%noinline
foo : (0 _ : Z = S Z) -> Void
foo _ impossible

%noinline
bah : (0 _ : Z = S Z) -> Void
bah prf = foo prf
data BadPrf = Ok | No (Z = S Z)

Show BadPrf where
    show Ok = "Ok"
    show (No prf) = absurd $ bah prf

main : IO ()
main = printLn Ok

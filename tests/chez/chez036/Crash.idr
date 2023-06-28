-- no_clauses.idr
%default total

bad : (0 _ : Z = S Z) -> Void
bad _ impossible

data BadPrf = Ok | No (Z = S Z)

Show BadPrf where
    show Ok = "Ok"
    show (No prf) = absurd $ bad prf

main : IO ()
main = printLn Ok

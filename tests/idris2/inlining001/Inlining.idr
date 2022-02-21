
leaveAlone : String -> String
leaveAlone x = x ++ "!"

%inline
forceInline : Nat -> Nat
forceInline y = y + 10

%noinline
public export
forceNoInline : Nat
forceNoInline = 10

public export
heuristicPublicInline : Nat
heuristicPublicInline = 2

%inline
export
exportedForced : Nat
exportedForced = 33

export
exportedUnforced : Nat
exportedUnforced = 66

IntOrChar : Bool -> Type
IntOrChar True = Int
IntOrChar False = Char

foo : Nat -> (x : Bool) -> IntOrChar x -> String
foo num x i
    = case x of
           True => show num
           False => show i

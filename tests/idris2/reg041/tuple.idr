tupleBug : Pair () a -> ()
tupleBug (_, (_, _)) = ()

odd : a -> Bool
odd () = False

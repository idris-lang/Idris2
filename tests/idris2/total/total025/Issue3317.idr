total
f : (a, List a) -> ()
f (_, []) = ()
f (x, _::xs) = f (x, xs)

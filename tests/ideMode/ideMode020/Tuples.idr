init : a -> c -> List b -> List (a, b, c)
init a c = map (uncurry (,)) . map (a,) . map (,c)

unzip : List (a, b) -> (List a, List b)
unzip [] = ([], [])
unzip ((a, b) :: abs)
  = let (as, bs) = unzip abs in
    (a :: as, b :: bs)

unzip4 : List (a, b, c, d) -> (List a, List b, List c, List d)
unzip4 [] = ([], [], [], [])
unzip4 (abcd :: abcds)
  = let (a, b, c, d) = abcd
        (as, bs, cs, ds) = unzip4 abcds
    in (a :: as, b :: bs, c :: cs, d :: ds)

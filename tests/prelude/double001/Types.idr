nan, inf : Double
nan = 0.0 / 0.0
inf = 1.0 / 0.0

powDoubleCases : List Double
powDoubleCases = [
    pow (-inf) (-inf),
    pow (-inf) (-2.5),
    pow (-inf) (-0.5),
    pow (-inf) 0,
    pow (-inf) 0.5,
    pow (-inf) 2.5,
    pow (-inf) inf,
    pow (-inf) nan,

    pow (-2.5) (-inf),
    pow (-2.5) (-2.5),
    pow (-2.5) (-0.5),
    pow (-2.5) 0,
    pow (-2.5) 0.5,
    pow (-2.5) 2.5,
    pow (-2.5) inf,
    pow (-2.5) nan,

    pow (-0.5) (-inf),
    pow (-0.5) (-2.5),
    pow (-0.5) (-0.5),
    pow (-0.5) 0,
    pow (-0.5) 0.5,
    pow (-0.5) 2.5,
    pow (-0.5) inf,
    pow (-0.5) nan,

    pow 0 (-inf),
    pow 0 (-2.5),
    pow 0 (-0.5),
    pow 0 0,
    pow 0 0.5,
    pow 0 2.5,
    pow 0 inf,
    pow 0 nan,

    pow 0.5 (-inf),
    pow 0.5 (-2.5),
    pow 0.5 (-0.5),
    pow 0.5 0,
    pow 0.5 0.5,
    pow 0.5 2.5,
    pow 0.5 inf,
    pow 0.5 nan,

    pow 2.5 (-inf),
    pow 2.5 (-2.5),
    pow 2.5 (-0.5),
    pow 2.5 0,
    pow 2.5 0.5,
    pow 2.5 2.5,
    pow 2.5 inf,
    pow 2.5 nan,

    pow inf (-inf),
    pow inf (-2.5),
    pow inf (-0.5),
    pow inf 0,
    pow inf 0.5,
    pow inf 2.5,
    pow inf inf,
    pow inf nan,

    pow nan (-inf),
    pow nan (-2.5),
    pow nan (-0.5),
    pow nan 0,
    pow nan 0.5,
    pow nan 2.5,
    pow nan inf,
    pow nan nan,
  ]

main : IO ()
main = traverse_ printLn powDoubleCases

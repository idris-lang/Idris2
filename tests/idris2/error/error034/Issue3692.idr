bad : Bool -> ()
bad True = ()

namespace X
  foo : ()
  foo = ()

mutual
  bar : ()
  bar = baz

  baz : ()
  baz = bar

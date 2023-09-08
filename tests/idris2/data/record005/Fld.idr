record Foo where
  constructor MkFoo
  {Gnu : Char}

AFoo : Foo
AFoo = MkFoo {Gnu = 'c'}

Bar : Foo
Bar = { Gnu := '?' } AFoo

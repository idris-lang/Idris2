
-- %default total

record Oops where
  constructor MkOops
  runOops : Not Oops

total
notOops : Not Oops
notOops x = runOops x x

-- total
oops : Oops
oops = MkOops notOops

total
boom : Void
boom = runOops oops oops

data Foo = MkFoo (Not Foo)

runFoo : Foo -> Not Foo
runFoo (MkFoo nf) = nf

notFoo : Not Foo
notFoo x = runFoo x x

foo : Foo
foo = MkFoo notFoo

total
boom2 : Void
boom2 = runFoo foo foo

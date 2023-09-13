
data Oops = MkOops (Not Oops)

total
runOops : Oops -> Not Oops
runOops (MkOops nf) = nf

total
notOops : Not Oops
notOops x = runOops x x

covering
oops : Oops
oops = MkOops notOops

total
boom : Void
boom = runOops oops oops

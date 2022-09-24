module Idris.Syntax.Builtin

import Core.Name

%default total

export
pairname : Name
pairname = NS builtinNS (UN $ Basic "Pair")

export
mkpairname : Name
mkpairname = NS builtinNS (UN $ Basic "MkPair")

export
dpairname : Name
dpairname = NS dpairNS (UN $ Basic "DPair")

export
mkdpairname : Name
mkdpairname = NS dpairNS (UN $ Basic "MkDPair")

export
nilName : Name
nilName = NS preludeNS (UN $ Basic "Nil")

export
consName : Name
consName = NS preludeNS (UN $ Op (MkOperator InfixR 7 "::"))

export
interpolateName : Name
interpolateName = NS preludeNS (UN $ Basic "interpolate")

export
eqName : Name
eqName = NS builtinNS (UN $ Op (MkOperator Infix 6 "==="))

export
heqName : Name
heqName = NS builtinNS (UN $ Op (MkOperator Infix 6 "~=~"))

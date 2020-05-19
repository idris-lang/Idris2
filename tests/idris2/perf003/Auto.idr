public export
data Phase = Gas | Liquid | Solid

public export
data ChangePhase : Phase -> Phase -> Type where
	Sequence : ChangePhase a b -> ChangePhase b c -> ChangePhase a c
	Condense : ChangePhase Gas Liquid
	Freeze : ChangePhase Liquid Solid
	Melt : ChangePhase Solid Liquid
	Vaporize : ChangePhase Liquid Gas
	Sublimate : ChangePhase Solid Gas

public export
inferred : { auto transition : ChangePhase l r } -> ChangePhase l r
inferred { transition } = transition

test : ChangePhase Gas Solid
test = inferred

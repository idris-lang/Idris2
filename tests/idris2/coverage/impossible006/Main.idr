eqPiData : {a : () -> ()} -> {b : Nat} -> Equal a b -> Void
eqPiData _ impossible

eqDataPi : {a : Nat} -> {b : () -> ()} -> Equal a b -> Void
eqDataPi _ impossible

eqPiPrim : {a : () -> ()} -> {b : String} -> Equal a b -> Void
eqPiPrim _ impossible

eqPrimPi : {a : String} -> {b : () -> ()} -> Equal a b -> Void
eqPrimPi _ impossible

eqPiType : {a : () -> ()} -> {b : Type} -> Equal a b -> Void
eqPiType _ impossible

eqTypePi : {a : Type} -> {b : () -> ()} -> Equal a b -> Void
eqTypePi _ impossible

module Core.Context.TTC

import Core.Binary
import Core.Context

%default covering

export
TTC BuiltinType where
    toBuf BuiltinNatural = tag 0
    toBuf NaturalToInteger = tag 1
    toBuf IntegerToNatural = tag 2
    fromBuf = case !getTag of
        0 => pure BuiltinNatural
        1 => pure NaturalToInteger
        2 => pure IntegerToNatural
        _ => corrupt "BuiltinType"

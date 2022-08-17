module Core.Context.TTC

import Core.Binary
import Core.TTC
import Core.Context

%default covering

export
TTC BuiltinType where
    toBuf b BuiltinNatural = tag 0
    toBuf b NaturalToInteger = tag 1
    toBuf b IntegerToNatural = tag 2
    fromBuf b = case !getTag of
        0 => pure BuiltinNatural
        1 => pure NaturalToInteger
        2 => pure IntegerToNatural
        _ => corrupt "BuiltinType"

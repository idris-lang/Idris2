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


export
TTC NoMangleDirective where
  toBuf b (CommonName n)
      = do tag 0; toBuf b n
  toBuf b (BackendNames ns)
      = do tag 1; toBuf b ns

  fromBuf b
      = case !getTag of
             0 => do n <- fromBuf b; pure (CommonName n)
             1 => do ns <- fromBuf b; pure (BackendNames ns)
             _ => corrupt "NoMangleDirective"

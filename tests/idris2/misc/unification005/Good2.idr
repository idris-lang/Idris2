record W where
  constructor MkW
  value : Unit

refocus : Pair Unit Unit -> W
refocus (MkPair MkUnit env) = MkW env

data Trace : W -> Type where
  Step : (r : W) -> Trace r

trace : (t : Unit) -> (env : W) -> Trace (refocus (MkPair t (value env))) -> Unit
trace MkUnit (MkW _) (Step (MkW env)) = MkUnit

data WrapUnit : Unit -> Type where
  MkWrapUnit : WrapUnit MkUnit -> WrapUnit MkUnit

extractUnit : (t : Unit) -> (WrapUnit t) -> Type
extractUnit MkUnit (MkWrapUnit tr) = extractUnit MkUnit tr

U : Unit
isUnit : Builtin.Equal U MkUnit

wrappedUnitIsUnit : (x: Unit) ->
              (trace : WrapUnit x) ->
              extractUnit x trace
wrappedUnitIsUnit MkUnit (MkWrapUnit trace)
  = wrappedUnitIsUnit U $ rewrite isUnit in trace

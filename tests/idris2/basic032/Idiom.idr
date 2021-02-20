export
record Core t where
  constructor MkCore
  runCore : IO (Either String t)

pure : a -> Core a
pure x = MkCore (pure (pure x))

export
(<*>) : Core (a -> b) -> Core a -> Core b
(<*>) (MkCore f) (MkCore a) = MkCore [| f `Applicative.(<*>)` a |]

addm : Maybe Int -> Maybe Int -> Maybe Int
addm x y = [| x + y |]

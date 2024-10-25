
record Mon (a : Type) where
  constructor MkMon
  empty : a
  combine : a -> a -> a

record MonLaws (a : Type) (mon : Mon a) where
  constructor MkR
  let (<+>) : a -> a -> a
      (<+>) = mon.combine
  left : (x : a) -> x <+> mon.empty === x
  right : (x : a) -> mon.empty <+> x === x


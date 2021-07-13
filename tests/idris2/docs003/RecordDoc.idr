module RecordDoc

record A (a : Type) where
  anA : a

record Tuple (a, b : Type) where
  proj1 : a
  proj2 : b

record Singleton {0 a : Type} (v : a) where
  value : a
  0 equal : value = v

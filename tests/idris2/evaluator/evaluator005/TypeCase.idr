data The : (a : Type) -> a -> Type where
  Is : (x : a) -> The a x

tcase : Type -> Type
tcase (The a _) = a
tcase a = a


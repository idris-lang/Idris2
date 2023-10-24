identity : (a : Type) -> a -> a
identity a = id

identityL :
  (a, b : Type )
  -> (f : a -> b)
  -> (identity b) . f = f
identityL a b f = Refl

identityR :
  (a, b : Type )
  -> (f : a -> b)
  -> f = (identity b) . f
identityR a b f = Refl

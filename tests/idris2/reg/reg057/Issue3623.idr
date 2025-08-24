export infix 0 <->

record (<->) (a, b : Type) where
  constructor Iff
  to  : a -> b
  from : b -> a

forall_one_point :
  (p : a -> Type) ->
  (forall x. x = t -> p x) <-> p t
forall_one_point p = Iff
  (\p_all => p_all Refl)
  (\p_t, p_eq => rewrite p_eq in p_t)

failing "Mismatch between: (p_eq : ?_) -> ?type_of_extra_arg and p x"
  forall_one_point_err :
    (p : a -> Type) ->
    (forall x. x = t -> p x) <-> p t
  forall_one_point_err p = Iff
    (\p_all => p_all Refl)
    (\p_t, x, p_eq => ?extra_arg)

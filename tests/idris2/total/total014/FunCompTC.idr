%default total

data X : Type where
  B : X
  T : r -> (r -> X) -> X

f_expl : (X -> X) -> X -> X
f_expl f B       = f B
f_expl f (T k g) = T k $ \n => f_expl f $ g n

f_impl : (X -> X) -> X -> X
f_impl f B       = f B
f_impl f (T k g) = T k $ f_impl f . g

idF : a -> a
idF = id

extensionality : (f : a -> b) -> (g : a -> b) -> ((x : a) -> f x = g x) -> f = g
extensionality f g = believe_me

leftIdPoint : (f : a -> b) -> (x : a) -> idF (f x) = f x
leftIdPoint f x = Refl

leftId : (f : a -> b) -> (idF . f = f)
leftId f = ?hole

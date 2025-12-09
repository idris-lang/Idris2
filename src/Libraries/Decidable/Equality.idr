module Libraries.Decidable.Equality

import public Decidable.Equality

public export
maybeEq : DecEq a => (x, y : a) -> Maybe (x = y)
maybeEq x y = case decEq x y of
                   Yes eq => Just eq
                   No _   => Nothing

%inline
public export
maybeCong : (f : a -> b) -> Maybe (x = y) -> Maybe (f x = f y)
maybeCong f = map (\eq => cong f eq)

%inline
public export
maybeCong2 : (f : a -> b -> c) -> Maybe (x = y) -> Maybe (v = w) -> Maybe (f x v = f y w)
maybeCong2 f mxy mvw = (\xy, vw => cong2 f xy vw) <$> mxy <*> mvw

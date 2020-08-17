infixl 0  ~~
prefix 1  |~
infix  1  ...

public export
(...) : (x : a) -> (y ~=~ x) -> (z : a ** y ~=~ z)
(...) x pf = (x ** pf)

public export
data FastDerivation : (x : a) -> (y : b) -> Type where
  (|~) : (x : a) -> FastDerivation x x
  (~~) : FastDerivation x y ->
         (step : (z : c ** y ~=~ z)) -> FastDerivation x z

public export
Calc : {x : a} -> {y : b} -> FastDerivation x y -> x = y
Calc (|~ x) = Refl
Calc {y} ((~~) {z=y} {y=y} der (MkDPair y Refl)) = Calc der

bad : Z = S Z
bad = Calc $ |~ Z ~~ Z ...(Refl)

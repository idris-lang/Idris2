module Main

namespace App2
  public export
  (<*>) : Applicative f => Applicative g =>
          f (g $ a -> b) -> f (g a) -> f (g b)
  fgf <*> fga = Prelude.[| fgf <*> fga |]

  public export
  pure : Applicative f => Applicative g =>
         a -> f (g a)
  pure = Prelude.pure . Prelude.pure

namespace App3
  public export
  (<*>) : Applicative f => Applicative g => Applicative h =>
          f (g (h $ a -> b)) -> f (g (h a)) -> f (g (h b))
  fgf <*> fga = App2.[| fgf <*> fga |]

  public export
  pure : Applicative f => Applicative g => Applicative h =>
         a -> f (g (h a))
  pure = App2.pure . Prelude.pure

list : List (Maybe Integer)
list = [Just 3, Just 7, Nothing, Just 0]

test2 : List (Maybe Integer)
test2 = App2.[| list + list |]

test3 : Either String (List (Maybe Integer))
test3 = App3.[| Right list + Right list |]

main : IO ()
main = printLn test2 >> printLn test3

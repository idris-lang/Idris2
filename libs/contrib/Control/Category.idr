module Control.Category

import Data.Morphisms


public export
interface Category (0 cat : obj -> obj -> Type) | cat where
  id  : cat a a
  (.) : cat b c -> cat a b -> cat a c

public export
Category Morphism where
  id                = Mor id
  -- disambiguation needed below, because unification can now get further
  -- here with Category.(.) and it's only interface resolution that fails!
  (Mor f) . (Mor g) = Mor $ Basics.(.) f g

public export
Monad m => Category (Kleislimorphism m) where
  id                        = Kleisli (pure . id)
  (Kleisli f) . (Kleisli g) = Kleisli $ \a => g a >>= f

infixr 1 >>>

public export
(>>>) : Category cat => cat a b -> cat b c -> cat a c
f >>> g = g . f

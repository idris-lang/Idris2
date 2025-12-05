import Control.Monad.Identity

foo : Identity (a -> Type) -> a -> Type
foo (Id f {a = .(a -> Type)}) x = f x

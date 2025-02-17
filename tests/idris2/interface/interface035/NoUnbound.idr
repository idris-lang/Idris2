%unbound_implicits off
interface Foo a where
interface Foo a => Bar (a : Type) where

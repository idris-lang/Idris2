data Cont : (r : Type) -> (a : Type) -> Type where
     MkCont : ((k : a -> r) -> r) -> Cont r a

data ContT : (r : Type) -> (m : Type -> Type) -> (a : Type) -> Type where
     MkContT : ((k : a -> m r) -> m r) -> ContT r m a

cbind : Cont r a -> (a -> Cont r b) -> Cont r b

ctbind : ContT r m a -> (a -> ContT r m b) -> ContT r m b

callCC : ((a -> ContT r m b) -> ContT r m a) -> ContT r m a

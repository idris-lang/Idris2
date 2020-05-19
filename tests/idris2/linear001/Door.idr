import Stuff

data Usage = Once | Many

data Unrestricted : Type -> Type where
     Un : (x : a) -> Unrestricted a

data Use : Usage -> (Type -> Type) -> Type -> Type where
     MkUse : m a -> Use l m a

contType : (Type -> Type) -> Usage -> Usage -> Type -> Type -> Type
contType m Once q a b = ((1 x : a) -> Use q m b)
contType m Many q a b = ((x : a) -> Use q m b)

(>>=) : (1 f : Use p m a) -> (1 k : contType m p q a b) -> Use q m b
pure : a -> Use u m a

One : (Type -> Type) -> Type -> Type
One = Use Once

Any : (Type -> Type) -> Type -> Type
Any = Use Many

data DoorState = Open | Closed

data Door : DoorState -> Type where
     MkDoor : (isOpen : Bool) -> Door doorstate

newDoor : One m (Door Closed)

knock : (1 d : Door Closed) -> One m (Door Closed)
openDoor : (1 d : Door Closed) -> One m (Either (Door Closed) (Door Open))
closeDoor : (1 d : Door Open) -> One m (Door Closed)

deleteDoor : (1 d : Door Closed) -> Any m ()

doorProg : Any m ()
doorProg
    = do d <- newDoor
         Right d <- openDoor d
            | Left d => deleteDoor d
         d <- closeDoor d
         deleteDoor d


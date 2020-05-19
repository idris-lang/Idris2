module Door

import Linear

data DoorState = Closed | Open

data Door : DoorState -> Type where
     MkDoor : (isOpen : Bool) -> Door (if isOpen then Open else Closed)

newDoor    : One m (Door Closed)
knock      : (1 d : Door t) -> One m (Door t)
openDoor   : (1 d : Door Closed) -> One m (Res Bool (\r => Door (if r then Open else Closed)))
closeDoor  : (1 d : Door Open) -> One m (Door Closed)
deleteDoor : (1 d : Door Closed) -> Any m ()

doorProg : Any m ()
doorProg
    = do d <- newDoor
         d <- knock d
         let x = the Int ?something
         ?bar

doorProg2 : Any m ()
doorProg2
    = do d <- newDoor
         d <- knock d
         let x = the Int ?something2
         d' <- knock d
         ?bar2

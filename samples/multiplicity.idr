import Data.Vect

append : Vect n a -> Vect m a -> Vect (n + m) a
append xs ys = ?append_rhs

data DoorState = Open | Closed

data Door : DoorState -> Type where
     MkDoor : (doorId : Int) -> Door st

openDoor : (1 d : Door Closed) -> Door Open
closeDoor : (1 d : Door Open) -> Door Closed

newDoor : (1 p : (1 d : Door Closed) -> IO ()) -> IO ()
deleteDoor : (1 d : Door Closed) -> IO ()

doorProg : IO ()
doorProg
    = newDoor $ \d =>
          let d' = openDoor d
              d'' = closeDoor d' in
              deleteDoor d''

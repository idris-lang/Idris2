import Control.Linear.LIO

foo : LinearIO io => L io ()
foo = do putStrLn "Hello"
         putStrLn "World"

data DoorState = CLOSED | OPEN

data OpenResult = Jammed | OK

data Door : DoorState -> Type where

newDoor : LinearIO io => (1 _ : (1 _ : Door CLOSED) -> L io ()) -> L io ()

openDoor : LinearIO io =>
           (1 _ : Door CLOSED) ->
           L io {use=1} (Res OpenResult (\case
                                           Jammed => Door CLOSED
                                           OK => Door OPEN))

closeDoor : LinearIO io => (1 _ : Door OPEN) -> L io {use=1} (Door CLOSED)
deleteDoor : LinearIO io => (1 _ : Door CLOSED) -> L io ()

doorProg : LinearIO io => L io ()
doorProg
    = newDoor $ \d =>
         do ok # d <- openDoor d
            case ok of
                 Jammed => deleteDoor d
                 OK => do d <- closeDoor d
                          putStrLn "Yay"
                          deleteDoor d

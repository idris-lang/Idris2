import Control.Linear.LIO

data Door : Type

data DoorState = OPEN | CLOSED

data DoorIs : DoorState -> Door -> Type where
     [noHints]
     MkDState : (d : Door) -> DoorIs st d

newDoor : L {use=1} IO (Res Door (DoorIs CLOSED))

openDoor : (d : Door) -> {auto 1 p : DoorIs CLOSED d} ->
           L {use=1} IO (Res Bool (const (DoorIs OPEN d)))

closeDoor : (d : Door) -> {auto 1 p : DoorIs OPEN d} ->
            L {use=1} IO (DoorIs CLOSED d)

deleteDoor : (d : Door) -> {auto 1 p : DoorIs CLOSED d} ->
             L IO ()

prog : L IO ()
prog = do d # p <- newDoor
          ok # p' <- openDoor d
          ?whatnow

prog2 : L IO ()
prog2 = do d # p <- newDoor
           ok # p' <- openDoor d
           p'' <- closeDoor d
           ?whatnow2

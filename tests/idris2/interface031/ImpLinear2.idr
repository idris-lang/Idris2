module ImpLinear2

data LRes : (a : Type) -> (a -> Type) -> Type where
     MkLRes : (result : a) ->
              (1 _ : t result) -> (1 w : %World) -> LRes a t

PrimL : (a : Type) -> (a -> Type) -> Type
PrimL a t = (1 x : %World) -> LRes a t

data LIO : (a : Type) -> (a -> Type) -> Type where
     MkLIO : (1 _ : PrimL a t) -> LIO a t

pure : (x : a) -> (1 _ : t x) => LIO a t
pure res = MkLIO (MkLRes res %search)

(>>=) : (1 _ : LIO a t) ->
        (1 _ : (x : a) -> (1 _ : t x) => LIO b t') ->
        LIO b t'
(>>=) (MkLIO fn) k
    = MkLIO $ \w =>
         let MkLRes x' tok' w' = fn w
             MkLIO res = k x' in
             res w'

(>>) : (1 _ : LIO () t) ->
       (1 _ : (1 _ : t ()) => LIO b t') ->
       LIO b t'
(>>) x k = (>>=) x (\() => k)

namespace Door
  export
  data Door = MkDoor

  public export
  data DoorState = CLOSED | OPEN

  export
  data DoorIs : DoorState -> Door -> Type where
       DState : DoorIs st d

  public export
  data Opened = OK | Jammed

  export
  withDoor : ((d : Door) -> (1 _ : DoorIs CLOSED d) =>
              LIO () (const (DoorIs CLOSED d))) ->
             LIO () (const ())

  export
  openDoor : (d : Door) -> (1 _ : DoorIs CLOSED d) =>
             LIO Opened (\case
                            OK => DoorIs OPEN d
                            Jammed => DoorIs CLOSED d)

  export
  closeDoor : (d : Door) -> (1 _ : DoorIs OPEN d) =>
              LIO () (const (DoorIs CLOSED d))

test : LIO () (const ())
test = withDoor $ \d =>
          do ok <- openDoor d
             case ok of
                  OK => do closeDoor d
                           ?openOK
                  Jammed => ?openBad

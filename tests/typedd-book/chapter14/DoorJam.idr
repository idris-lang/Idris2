data DoorState = DoorClosed | DoorOpen

data DoorResult = OK | Jammed

data DoorCmd : (ty : Type) ->
               DoorState ->
               (ty -> DoorState) ->
               Type where
  Open :     DoorCmd DoorResult DoorClosed (\res => case res of
                                                         OK => DoorOpen
                                                         Jammed => DoorClosed)
  Close :    DoorCmd ()         DoorOpen   (const DoorClosed)
  RingBell : DoorCmd ()         DoorClosed (const DoorClosed)

  Display : String -> DoorCmd () state (const state)

  Pure : (res : ty) -> DoorCmd ty (state_fn res) state_fn
  (>>=) : DoorCmd a state1 state2_fn ->
          ((res: a) -> DoorCmd b (state2_fn res) state3_fn) ->
          DoorCmd b state1 state3_fn

logOpen : DoorCmd DoorResult DoorClosed
                             (\res => case res of
                                           OK => DoorOpen
                                           Jammed => DoorClosed)
logOpen = do Display "Trying to open the door"
             OK <- Open | Jammed => do Display "Jammed"
                                       Pure Jammed
             Display "Success"
             Pure OK

doorProg : DoorCmd () DoorClosed (const DoorClosed)
doorProg = do RingBell
              jam <- Open
              Display "Trying to open the door"
              case jam of
                   OK => do Display "Glad To Be Of Service"
                            Close
                   Jammed => Display "Door Jammed"

doorProg2 : DoorCmd () DoorClosed (const DoorClosed)
doorProg2 = do RingBell
               OK <- Open | Jammed => Display "Door Jammed"
               Display "Glad To Be Of Service"
               Close
               OK <- Open | Jammed => Display "Door Jammed"
               Display "Glad To Be Of Service"
               Close

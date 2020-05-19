module Linear

public export
data Usage = Once | Many

public export
data Lin : (Type -> Type) -> Usage -> Type -> Type where
     Pure : (1 x : a) -> Lin m usage a
     Lift : (1 x : m a) -> Lin m Many a
     BindOnce : (1 act : Lin m Once a) ->
                (1 k : (1 x : a) -> Lin m t b) -> Lin m t b
     BindMany : (1 act : Lin m Many a) ->
                (1 k : (x : a) -> Lin m t b) -> Lin m t b

public export
data Unrestricted : Type -> Type where
     MkUn : (x : a) -> Unrestricted a

export
pure : (1 x : a) -> Lin m usage a
pure = Pure

export
lift : (1 x : m a) -> Lin m Many a
lift = Lift

public export
contType : (Type -> Type) -> Usage -> Usage -> Type -> Type -> Type
contType m Once q a b = (1 x : a) -> Lin m q b
contType m Many q a b = (x : a) -> Lin m q b

public export
(>>=) : {p : _} ->
        (1 f : Lin m p a) -> (1 k : contType m p q a b) -> Lin m q b
(>>=) {p=Once} = BindOnce
(>>=) {p=Many} = BindMany

export
run : Monad m => Lin m usage t -> m t
run (Pure x) = pure x
run (Lift p) = p
run (BindOnce act k)
    = do act' <- run act
         run (k act')
run (BindMany act k)
    = do act' <- run act
         run (k act')

public export
One : (Type -> Type) -> Type -> Type
One m = Lin m Once

public export
Any : (Type -> Type) -> Type -> Type
Any m = Lin m Many

infix 2 @@

public export
data Res : (a : Type) -> (a -> Type) -> Type where
     (@@) : (val : a) -> (1 resource : r val) -> Res a r


{-
data DoorState = Closed | Open

data Door : DoorState -> Type where
     MkDoor : (isOpen : Bool) -> Door (if isOpen then Open else Closed)

newDoor    : One m (Door Closed)
knock      : (1 d : Door t)      -> One m (Door t)
openDoor   : (1 d : Door Closed) -> One m (Res Bool (\ok => Door (if ok then Open else Closed)))
closeDoor  : (1 d : Door Open)   -> One m (Door Closed)
deleteDoor : (1 d : Door Closed) -> Any m ()

doorProg : Any m ()
doorProg
    = do d <- newDoor
         ok @@ d' <- openDoor d
         d'' <- knock d'
         if ok
            then ?doorOK
            else ?doorBad
            -}

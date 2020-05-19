> data Usage = Once | Many

> data Use : Usage -> (Type -> Type) -> Type -> Type where
>      Pure : (1 x : a) -> Use t m a
>      BindOnce : (1 act : Use Once m a) -> (1 k : (1 x : a) -> Use t m b) -> Use t m b
>      BindMany : (1 act : Use Many m a) -> (1 k : (x : a) -> Use t m b) -> Use t m b

> contType : (Type -> Type) -> Usage -> Usage -> Type -> Type -> Type
> contType m Once q a b = ((1 x : a) -> Use q m b)
> contType m Many q a b = ((x : a) -> Use q m b)

> (>>=) : {p : _} -> (1 f : Use p m a) -> (1 k : contType m p q a b) -> Use q m b
> (>>=) {p = Once} = BindOnce
> (>>=) {p = Many} = BindMany

> pure : (1 x : a) -> Use t m a
> pure = Pure

> One : (Type -> Type) -> Type -> Type
> One = Use Once

> Any : (Type -> Type) -> Type -> Type
> Any = Use Many

> infix 2 @@

> data Res : (a : Type) -> (a -> Type) -> Type where
>      (@@) : (x : a) -> (1 res : r x) -> Res a r

> data DoorState = Closed | Open

> data Door : DoorState -> Type where
>      MkDoor : (isOpen : Bool) -> Door (if isOpen then Open else Closed)

> newDoor : One m (Door Closed)
> newDoor = pure (MkDoor False)

> knock : (1 d : Door Closed) -> One m (Door Closed)
> openDoor : (1 d : Door Closed) ->
>            One m (Res Bool (\r => Door (if r then Open else Closed)))

> closeDoor : (1 d : Door Open) -> One m (Door Closed)

> deleteDoor : (1 d : Door Closed) -> Any m ()

> doorProg : Any m ()
> doorProg
>     = do d <- newDoor
>          r <- openDoor d
>          let x = 42
>          case r of
>               what => ?now

> doorProg2 : Any m ()
> doorProg2
>     = do d <- newDoor
>          r <- openDoor d
>          let x = 42
>          case r of
>               (res @@ d) => ?now_1

> doorProg3 : Any m ()
> doorProg3
>     = do d <- newDoor
>          r <- openDoor d
>          let x = 42
>          case r of
>               (True @@ d) => ?now_2
>               (False @@ d) => ?now_3

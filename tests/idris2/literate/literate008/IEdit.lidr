> natElim : (p : Nat -> Type) -> p Z -> ((k : Nat) -> p k -> p (S k)) ->
>           (x : Nat) -> p x

> natElim2 : (p : Nat -> Type) -> p Z -> ((k : Nat) -> p k -> p (S k)) ->
>            (x : Nat) -> p x
> natElim2 p x f Z = x
> natElim2 p x f (S k) = ?foo

> listElim : (p : List a -> Type) ->
>            (mnil : p []) ->
>            (mcons : (x : _) -> (xs : List a) -> p xs -> p (x :: xs)) ->
>            (xs : List a) -> p xs

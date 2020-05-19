data Vect : Nat -> Type -> Type where
     Nil  : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

append : Vect n a -> Vect m a -> Vect (n + m) a
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

-- Primarily to check the number of cases in the totality checker doesn't
-- explode because of all the Nils and Nats
funny : Vect 4 Bool -> Int
funny [False, False, False, False] = 0
funny [False, False, False, True] = 1
funny [False, False, True, False] = 2
funny [False, False, True, True] = 3
funny [False, True, False, False] = 4
funny [False, True, False, True] = 5
funny [False, True, True, False] = 6
funny [False, True, True, True] = 7
funny [True, False, False, False] = 8
funny [True, False, False, True] = 0
funny [True, False, True, False] = 10
funny [True, False, True, True] = 11
funny [True, True, False, False] = 12
funny [True, True, False, True] = 13
funny [True, True, True, False] = 14
funny [True, True, True, True] = 15

notFunny : Vect 4 Bool -> Int
notFunny [False, False, False, False] = 0
notFunny [False, False, False, True] = 1
notFunny [False, False, True, False] = 2
-- notFunny [False, False, True, True] = 3
notFunny [False, True, False, False] = 4
notFunny [False, True, False, True] = 5
notFunny [False, True, True, False] = 6
-- notFunny [False, True, True, True] = 7
notFunny [True, False, False, False] = 8
notFunny [True, False, False, True] = 0
notFunny [True, False, True, False] = 10
notFunny [True, False, True, True] = 11
notFunny [True, True, False, False] = 12
notFunny [True, True, False, True] = 13
notFunny [True, True, True, False] = 14
notFunny [True, True, True, True] = 15

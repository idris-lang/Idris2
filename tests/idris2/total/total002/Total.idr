data Fin : Nat -> Type where
     FZ : Fin (S k)
     FS : Fin k -> Fin (S k)

noFinZ : Fin Z -> Void
noFinZ FZ impossible
noFinZ (FS k) impossible

noFinZ' : Fin Z -> Void
noFinZ' x impossible

noEmpty : Void -> Fin Z
noEmpty t impossible

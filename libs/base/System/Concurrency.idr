module System.Concurrency

%default total

-- Futures based Concurrency and Parallelism

export
data Future : Type -> Type where [external]

%extern prim__makeFuture : {0 a : Type} -> Lazy a -> Future a
%foreign "racket:blodwen-await-future"
         "scheme:blodwen-await-future"
prim__awaitFuture : {0 a : Type} -> Future a -> a

export
fork : Lazy a -> Future a
fork = prim__makeFuture

export
forkIO : IO a -> Future a
forkIO a = fork $ unsafePerformIO a

export
await : Future a -> a
await f = prim__awaitFuture f

public export
Functor Future where
  map func future = fork $
    let result = await future in func result

public export
Applicative Future where
  pure v = fork v
  funcF <*> v = fork $
    let result = await v
        func   = await funcF in
        func result

public export
Monad Future where
  join = map await
  v >>= func = join $ fork $
    let result = await v in func result

module System.Future

%default total

-- Futures based Concurrency and Parallelism

export
data Future : Type -> Type where [external]

%foreign "scheme:blodwen-make-future"
prim__makeFuture : {0 a : Type} -> (() -> a) -> Future a

%foreign "scheme:blodwen-await-future"
prim__awaitFuture : {0 a : Type} -> Future a -> a

export %inline -- inlining is important for correct context in codegens
fork : Lazy a -> Future a
fork l = prim__makeFuture $ \_ => force l

export %inline -- inlining is important for correct context in codegens
await : Future a -> a
await f = prim__awaitFuture f

public export
Functor Future where
  map func future = fork $ func (await future)

public export
Applicative Future where
  pure v = fork v
  funcF <*> v = fork $ (await funcF) (await v)

public export
Monad Future where
  join = map await
  v >>= func = join . fork $ func (await v)

export
performFutureIO : HasIO io => Future (IO a) -> io (Future a)
performFutureIO = primIO . prim__io_pure . map unsafePerformIO

export
forkIO : HasIO io => IO a -> io (Future a)
forkIO a = performFutureIO $ fork a

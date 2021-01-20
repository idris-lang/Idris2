module Debug.Panic

import System

||| Print message and exit with error.
export
panic : HasIO io => (message : String) -> io Void
panic message = do
  -- TODO: print to stderr
  putStrLn ("assertion failed: " ++ message)
  exitFailure

||| Print message and exit with error.
||| This is an unsafe function, because it makes evaluation not pure.
export
unsafePanic : (message : String) -> Void
unsafePanic message = unsafePerformIO im where
  im : IO Void
  im = do v <- panic message
          pure v

||| Perform runtime assertion: exit if condition is false.
export
rtassert : HasIO io => (cond : Bool) -> (message : Lazy String) -> io ()
rtassert True message = pure ()
rtassert False message = do v <- panic message
                            pure (void v)

||| Perform runtime assrtion in pure expressions.
||| This is an unsafe function, because it makes evaluation not pure.
export
unsafeRtassert : (cond : Bool) -> (message : Lazy String) -> (result : a) -> a
unsafeRtassert cond message result = unsafePerformIO im where
  im : IO a
  im = do rtassert cond message
          pure result

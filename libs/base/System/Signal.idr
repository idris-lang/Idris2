module System.Signal

%default total

signalFFI : String -> String
signalFFI fn = "C:" ++ fn ++ ", libidris2_support, idris_signal.h"

--
-- Signals
--
%foreign signalFFI "sighup"
prim__sighup : Int

%foreign signalFFI "sigint"
prim__sigint : Int

%foreign signalFFI "sigquit"
prim__sigquit : Int

%foreign signalFFI "sigill"
prim__sigill : Int

%foreign signalFFI "sigsegv"
prim__sigsegv : Int

%foreign signalFFI "sigtrap"
prim__sigtrap : Int

%foreign signalFFI "sigfpe"
prim__sigfpe : Int

%foreign signalFFI "sigusr1"
prim__sigusr1 : Int

%foreign signalFFI "sigusr2"
prim__sigusr2 : Int

public export
data Signal = ||| Hangup (i.e. controlling terminal closed)
              SigHUP
            | ||| Interrupt (e.g. ctrl+c pressed)
              SigINT
            | ||| Quit
              SigQUIT
            | ||| Ill-formed instruction
              SigILL
            | ||| Segmentation fault
              SigSEGV
            | ||| Trap (as used by debuggers)
              SigTRAP
            | ||| Floating-point error
              SigFPE
            | SigUser1
            | SigUser2

Eq Signal where
  SigHUP   == SigHUP   = True
  SigINT   == SigINT   = True
  SigQUIT  == SigQUIT  = True
  SigILL   == SigILL   = True
  SigSEGV  == SigSEGV  = True
  SigTRAP  == SigTRAP  = True
  SigFPE   == SigFPE   = True
  SigUser1 == SigUser1 = True
  SigUser2 == SigUser2 = True
  _ == _ = False

signalCode : Signal -> Int
signalCode SigHUP   = prim__sighup
signalCode SigINT   = prim__sigint
signalCode SigQUIT  = prim__sigquit
signalCode SigILL   = prim__sigill
signalCode SigSEGV  = prim__sigsegv
signalCode SigTRAP  = prim__sigtrap
signalCode SigFPE   = prim__sigfpe
signalCode SigUser1 = prim__sigusr1
signalCode SigUser2 = prim__sigusr2

toSignal : Int -> Maybe Signal
toSignal (-1) = Nothing
toSignal x    = foldr matchCode Nothing codes
  where
    matchCode : (Int, Signal) -> Maybe Signal -> Maybe Signal
    matchCode x (Just y) = Just y
    matchCode (code, sig) Nothing = case x == code of
                                         True  => Just sig
                                         False => Nothing

    codes : List (Int, Signal)
    codes = [
              (prim__sighup , SigHUP)
            , (prim__sigint , SigINT)
            , (prim__sigquit, SigQUIT)
            , (prim__sigill , SigILL)
            , (prim__sigsegv, SigSEGV)
            , (prim__sigtrap, SigTRAP)
            , (prim__sigfpe , SigFPE)
            , (prim__sigusr1, SigUser1)
            , (prim__sigusr2, SigUser2)
            ]

--
-- Signal Handling
--
%foreign signalFFI "ignore_signal"
prim__ignoreSignal : Int -> PrimIO Int

%foreign signalFFI "default_signal"
prim__defaultSignal : Int -> PrimIO Int

%foreign signalFFI "collect_signal"
prim__collectSignal : Int -> PrimIO Int

%foreign signalFFI "handle_next_collected_signal"
prim__handleNextCollectedSignal : PrimIO Int

%foreign "C:idris2_getErrno, libidris2_support, idris_support.h"
prim__getErrorNo : PrimIO Int

||| An Error represented by a code. See
||| relevant `errno` documentation.
||| https://man7.org/linux/man-pages/man3/errno.3.html
export
data SignalError = Error Int

getError : HasIO io => io SignalError
getError = Error <$> primIO prim__getErrorNo

isError : Int -> Bool
isError (-1) = True
isError _    = False

||| Ignore the given signal.
||| Be careful doing this, as most signals have useful
||| default behavior -- you might want to set the signal
||| to its default behavior instead with `defaultSignal`.
export
ignoreSignal : HasIO io => Signal -> io (Either SignalError ())
ignoreSignal sig = do
  res <- primIO $ prim__ignoreSignal (signalCode sig)
  case isError res of
       False => pure $ Right ()
       True  => Left <$> getError

||| Use the default handler for the given signal.
||| You can use this function to unset custom
||| handling of a signal.
export
defaultSignal : HasIO io => Signal -> io (Either SignalError ())
defaultSignal sig = do
  res <- primIO $ prim__defaultSignal (signalCode sig)
  case isError res of
       False => pure $ Right ()
       True  => Left <$> getError

||| Collect the given signal.
|||
||| This replaces the existing handling of the given signal
||| and instead results in Idris collecting occurrences of
||| the signal until you call `handleNextCollectedSignal`.
export
collectSignal : HasIO io => Signal -> io (Either SignalError ())
collectSignal sig = do
  res <- primIO $ prim__collectSignal (signalCode sig)
  case isError res of
       False => pure $ Right ()
       True  => Left <$> getError

||| Get next collected signal under the pretense of handling it.
|||
||| Calling this "marks" the signal as handled so the next time
||| this function is called you will retrieve the next unhandled
||| signal instead of the same signal again.
|||
||| You get back Nothing if there are no pending signals.
export
handleNextCollectedSignal : HasIO io => io (Maybe Signal)
handleNextCollectedSignal =
  toSignal <$> primIO prim__handleNextCollectedSignal

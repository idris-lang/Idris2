||| Signal raising and handling.
|||
||| NOTE that there are important differences between
||| what can be done out-of-box in Windows and POSIX based
||| operating systems. This module tries to honor both
||| by putting things only available in POSIX environments
||| into appropriately named namespaces or data types.
module System.Signal

import Data.Fuel
import Data.List
import System.Errno

%default total

signalFFI : String -> String
signalFFI fn = "C:" ++ fn ++ ", libidris2_support, idris_signal.h"

signalFFINode : String -> String
signalFFINode fn = "node:support:" ++ fn ++ ",support_system_signal"

--
-- Signals
--
%foreign signalFFI "sighup"
         signalFFINode "sighup"
prim__sighup : Int

%foreign signalFFI "sigint"
         signalFFINode "sigint"
prim__sigint : Int

%foreign signalFFI "sigabrt"
         signalFFINode "sigabrt"
prim__sigabrt : Int

%foreign signalFFI "sigquit"
         signalFFINode "sigquit"
prim__sigquit : Int

%foreign signalFFI "sigill"
         signalFFINode "sigill"
prim__sigill : Int

%foreign signalFFI "sigsegv"
         signalFFINode "sigsegv"
prim__sigsegv : Int

%foreign signalFFI "sigtrap"
         signalFFINode "sigtrap"
prim__sigtrap : Int

%foreign signalFFI "sigfpe"
         signalFFINode "sigfpe"
prim__sigfpe : Int

%foreign signalFFI "sigusr1"
         signalFFINode "sigusr1"
prim__sigusr1 : Int

%foreign signalFFI "sigusr2"
         signalFFINode "sigusr2"
prim__sigusr2 : Int

public export
data PosixSignal = ||| Hangup (i.e. controlling terminal closed)
                   SigHUP
                 | ||| Quit
                   SigQUIT
                 | ||| Trap (as used by debuggers)
                   SigTRAP
                 | SigUser1
                 | SigUser2

export
Eq PosixSignal where
  SigHUP   == SigHUP   = True
  SigQUIT  == SigQUIT  = True
  SigTRAP  == SigTRAP  = True
  SigUser1 == SigUser1 = True
  SigUser2 == SigUser2 = True
  _ == _ = False

public export
data Signal = ||| Interrupt (e.g. ctrl+c pressed)
              SigINT
            | ||| Abnormal termination
              SigABRT
            | ||| Ill-formed instruction
              SigILL
            | ||| Segmentation fault
              SigSEGV
            | ||| Floating-point error
              SigFPE
            | ||| Signals only available on POSIX operating systems
              SigPosix PosixSignal

export
Eq Signal where
  SigINT   == SigINT   = True
  SigABRT  == SigABRT  = True
  SigILL   == SigILL   = True
  SigSEGV  == SigSEGV  = True
  SigFPE   == SigFPE   = True
  SigPosix x == SigPosix y = x == y
  _ == _ = False

signalCode : Signal -> Int
signalCode SigINT   = prim__sigint
signalCode SigABRT  = prim__sigabrt
signalCode SigILL   = prim__sigill
signalCode SigSEGV  = prim__sigsegv
signalCode SigFPE   = prim__sigfpe
signalCode (SigPosix SigHUP  ) = prim__sighup
signalCode (SigPosix SigQUIT ) = prim__sigquit
signalCode (SigPosix SigTRAP ) = prim__sigtrap
signalCode (SigPosix SigUser1) = prim__sigusr1
signalCode (SigPosix SigUser2) = prim__sigusr2

toSignal : Int -> Maybe Signal
toSignal (-1) = Nothing
toSignal x    = lookup x codes
  where
    codes : List (Int, Signal)
    codes = [
              (prim__sigint , SigINT)
            , (prim__sigabrt, SigABRT)
            , (prim__sigill , SigILL)
            , (prim__sigsegv, SigSEGV)
            , (prim__sigfpe , SigFPE)
            , (prim__sighup , SigPosix SigHUP)
            , (prim__sigquit, SigPosix SigQUIT)
            , (prim__sigtrap, SigPosix SigTRAP)
            , (prim__sigusr1, SigPosix SigUser1)
            , (prim__sigusr2, SigPosix SigUser2)
            ]

--
-- Signal Handling
--
%foreign signalFFI "ignore_signal"
         signalFFINode "ignoreSignal"
prim__ignoreSignal : Int -> PrimIO Int

%foreign signalFFI "default_signal"
         signalFFINode "defaultSignal"
prim__defaultSignal : Int -> PrimIO Int

%foreign signalFFI "collect_signal"
         signalFFINode "collectSignal"
prim__collectSignal : Int -> PrimIO Int

%foreign signalFFI "handle_next_collected_signal"
         signalFFINode "handleNextCollectedSignal"
prim__handleNextCollectedSignal : PrimIO Int

%foreign signalFFI "send_signal"
         signalFFINode "sendSignal"
prim__sendSignal : Int -> Int -> PrimIO Int

%foreign signalFFI "raise_signal"
         signalFFINode "raiseSignal"
prim__raiseSignal : Int -> PrimIO Int

||| An Error represented by a code. See
||| relevant `errno` documentation.
||| https://man7.org/linux/man-pages/man3/errno.3.html
public export
data SignalError = Error Int

getError : HasIO io => io SignalError
getError = Error <$> getErrno

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
|||
||| First, call `collectSignal` for any number of signals.
||| Then, call `handleNextCollectedSignal` in each main loop
||| of your program to retrieve (and mark as handled) the next
||| signal that was collected, if any.
|||
||| Signals are not queued, so the return order of signals is
||| not specified and signals may be deduplicated.
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

||| Get many collected signals and mark them as handled.
|||
||| Use `forever` as your fuel if you don't want or need to
||| retain totality. Alternatively, pick a max number to
||| retrieve and use `limit/1` as your fuel.
export
handleManyCollectedSignals : HasIO io => Fuel -> io (List Signal)
handleManyCollectedSignals Dry = pure []
handleManyCollectedSignals (More fuel) = do
  Just next <- handleNextCollectedSignal
    | Nothing => pure []
  pure $ next :: !(handleManyCollectedSignals fuel)

||| Send a signal to the current process.
export
raiseSignal : HasIO io => Signal -> io (Either SignalError ())
raiseSignal sig = do
  res <- primIO $ prim__raiseSignal (signalCode sig)
  case isError res of
       False => pure $ Right ()
       True  => Left <$> getError

namespace Posix
  ||| Send a signal to a POSIX process using a PID to identify the process.
  export
  sendSignal : HasIO io => Signal -> (pid : Int) -> io (Either SignalError ())
  sendSignal sig pid = do
    res <- primIO $ prim__sendSignal pid (signalCode sig)
    case isError res of
         False => pure $ Right ()
         True  => Left <$> getError

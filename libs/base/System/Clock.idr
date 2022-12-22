||| Types and functions for reasoning about time.
module System.Clock

import Data.Nat
import Data.String
import PrimIO

%default total

||| The various types of system clock available.
public export
data ClockType
  = ||| The time elapsed since the "epoch:" 00:00:00 UTC, January 1, 1970
    UTC
  | ||| The time elapsed since some arbitrary point in the past
    Monotonic
  | ||| Representing a time duration.
    Duration
  | ||| The amount of CPU time used by the current process.
    Process
  | ||| The amount of CPU time used by the current thread.
    Thread
  | ||| The current process's CPU time consumed by the garbage collector.
    GCCPU
  | ||| The current process's real time consumed by the garbage collector.
    GCReal

export
Show ClockType where
  show UTC       = "UTC"
  show Monotonic = "monotonic"
  show Duration  = "duration"
  show Process   = "process"
  show Thread    = "thread"
  show GCCPU     = "gcCPU"
  show GCReal    = "gcReal"

||| A clock recording some time in seconds and nanoseconds. The "type" of time
||| recorded is indicated by the given `ClockType`.
public export
data Clock : (type : ClockType) -> Type where
  MkClock
    : {type : ClockType}
    -> (seconds : Integer)
    -> (nanoseconds : Integer)
    -> Clock type

public export
Eq (Clock type) where
  (MkClock seconds1 nanoseconds1) == (MkClock seconds2 nanoseconds2) =
    seconds1 == seconds2 && nanoseconds1 == nanoseconds2

public export
Ord (Clock type) where
  compare (MkClock seconds1 nanoseconds1) (MkClock seconds2 nanoseconds2) =
  case compare seconds1 seconds2 of
    LT => LT
    GT => GT
    EQ => compare nanoseconds1 nanoseconds2

public export
Show (Clock type) where
  show (MkClock {type} seconds nanoseconds) =
    show type ++ ": " ++ show seconds ++ "s " ++ show nanoseconds ++ "ns"

||| Display a `Clock`'s content, padding the seconds and nanoseconds as
||| appropriate.
|||
||| @ s   the number of digits used to display the seconds
||| @ ns  the number of digits used to display the nanosecondns
||| @ clk the Clock whose contents to display
export
showTime : (s, ns : Nat) -> (clk : Clock type) -> String
showTime s ns (MkClock seconds nanoseconds) =
  let seconds' = show seconds
      nanoseconds' = show nanoseconds
  in concat [ padLeft s '0' seconds'
            , if ns == 0 then "" else "."
            , padRight ns '0' $ substr 0 ns $ (padLeft 9 '0' nanoseconds')
            , "s"
            ]

||| A helper to deconstruct a Clock.
public export
seconds : Clock type -> Integer
seconds (MkClock s _) = s

||| A helper to deconstruct a Clock.
public export
nanoseconds : Clock type -> Integer
nanoseconds (MkClock _ ns) = ns

||| Make a duration value.
|||
||| @ s  the number of seconds in the duration
||| @ ns the number of nanoseconds in the duration
public export
makeDuration : (s : Integer) -> (ns : Integer) -> Clock Duration
makeDuration = MkClock

||| Opaque clock value manipulated by the back-end.
data OSClock : Type where [external]

||| Note: Backends are required to implement UTC, monotonic time, CPU time in
||| current process/thread, and time duration; the rest are optional.
export
data ClockTypeMandatory
  = Mandatory
  | Optional

||| Determine whether the specified `ClockType` is required to be implemented by
||| all backends.
public export
isClockMandatory : ClockType -> ClockTypeMandatory
isClockMandatory GCCPU  = Optional
isClockMandatory GCReal = Optional
isClockMandatory _      = Mandatory

%foreign "scheme:blodwen-clock-time-monotonic"
         "RefC:clockTimeMonotonic"
         "javascript:lambda:()=>performance.now()" -- javascript clocks are represented as milliseconds
prim__clockTimeMonotonic : PrimIO OSClock

||| Get the current backend's monotonic time.
clockTimeMonotonic : IO OSClock
clockTimeMonotonic = fromPrim prim__clockTimeMonotonic

%foreign "scheme:blodwen-clock-time-utc"
         "RefC:clockTimeUtc"
         "javascript:lambda:()=>Date.now()"
prim__clockTimeUtc : PrimIO OSClock

||| Get the current UTC time.
clockTimeUtc : IO OSClock
clockTimeUtc = fromPrim prim__clockTimeUtc

%foreign "scheme:blodwen-clock-time-process"
         "RefC:clockTimeProcess"
         "javascript:support:clockTimeProcess,support_system_clock"
prim__clockTimeProcess : PrimIO OSClock

||| Get the amount of time used by the current process.
clockTimeProcess : IO OSClock
clockTimeProcess = fromPrim prim__clockTimeProcess

%foreign "scheme:blodwen-clock-time-thread"
         "RefC:clockTimeThread"
         "javascript:support:clockTimeThread,support_system_clock"
prim__clockTimeThread : PrimIO OSClock

||| Get the amount of time used by the current thread.
clockTimeThread : IO OSClock
clockTimeThread = fromPrim prim__clockTimeThread

%foreign "scheme:blodwen-clock-time-gccpu"
         "RefC:clockTimeGcCpu"
         "javascript:lambda:()=>null"
prim__clockTimeGcCpu : PrimIO OSClock

||| Get the amount of the current process's CPU time consumed by the garbage
||| collector.
clockTimeGcCpu : IO OSClock
clockTimeGcCpu = fromPrim prim__clockTimeGcCpu

%foreign "scheme:blodwen-clock-time-gcreal"
         "RefC:clockTimeGcReal"
         "javascript:lambda:()=>null"
prim__clockTimeGcReal : PrimIO OSClock

||| Get the amount of the current process's real-time consumed by the garbage
||| collector.
clockTimeGcReal : IO OSClock
clockTimeGcReal = fromPrim prim__clockTimeGcReal

fetchOSClock : ClockType -> IO OSClock
fetchOSClock UTC       = clockTimeUtc
fetchOSClock Monotonic = clockTimeMonotonic
fetchOSClock Process   = clockTimeProcess
fetchOSClock Thread    = clockTimeThread
fetchOSClock GCCPU     = clockTimeGcCpu
fetchOSClock GCReal    = clockTimeGcReal
fetchOSClock Duration  = clockTimeMonotonic

%foreign "scheme:blodwen-is-time?"
         "RefC:clockValid"
         "javascript:lambda:(x)=>x===null?0:1"
prim__osClockValid : OSClock -> PrimIO Int

||| A test to determine the status of optional clocks.
osClockValid : OSClock -> IO Int
osClockValid clk = fromPrim (prim__osClockValid clk)

%foreign "scheme:blodwen-clock-second"
         "RefC:clockSecond"
         "javascript:lambda:(x)=>BigInt(Math.floor(x/1000))"
prim__osClockSecond : OSClock -> PrimIO Bits64

||| Get the second of time from the given `OSClock`.
osClockSecond : OSClock -> IO Bits64
osClockSecond clk = fromPrim (prim__osClockSecond clk)

%foreign "scheme:blodwen-clock-nanosecond"
         "RefC:clockNanosecond"
         "javascript:lambda:(x)=>BigInt(Math.floor((x%1000)*1000*1000))"
prim__osClockNanosecond : OSClock -> PrimIO Bits64

||| Get the nanosecond of time from the given `OSClock`.
osClockNanosecond : OSClock -> IO Bits64
osClockNanosecond clk = fromPrim (prim__osClockNanosecond clk)

||| Convert an `OSClock` to an Idris `Clock`.
fromOSClock : {type : ClockType} -> OSClock -> IO (Clock type)
fromOSClock clk =
  pure $
    MkClock
      {type}
      (cast !(osClockSecond clk))
      (cast !(osClockNanosecond clk))

||| The return type of a function using a `Clock` depends on the type of
||| `Clock`:
||| * `Optional` clocks may not be implemented, so we might not return anything
||| * `Mandatory` clocks have to be implemented, so we _will_ return something
public export
clockTimeReturnType : (typ : ClockType) -> Type
clockTimeReturnType typ with (isClockMandatory typ)
  clockTimeReturnType typ | Optional = Maybe (Clock typ)
  clockTimeReturnType typ | Mandatory = Clock typ

||| Fetch the system clock of a given kind. If the clock is mandatory,
||| we return a `Clock type` else, we return a `Maybe (Clock type)`.
public export
clockTime : (typ : ClockType) -> IO (clockTimeReturnType typ)
clockTime clockType with (isClockMandatory clockType)
  clockTime clockType | Mandatory = fetchOSClock clockType >>= fromOSClock
  clockTime clockType | Optional = do
    clk <- fetchOSClock clockType
    valid <- map (== 1) $ osClockValid clk
    if valid
      then map Just $ fromOSClock clk
      else pure Nothing

||| Convert the time in the given clock to nanoseconds.
public export
toNano : Clock type -> Integer
toNano (MkClock seconds nanoseconds) =
  let scale = 1000000000
   in scale * seconds + nanoseconds

||| Convert some time in nanoseconds to a `Clock` containing that time.
|||
||| @ n the time in nanoseconds
public export
fromNano : {type : ClockType} -> (n : Integer) -> Clock type
fromNano n =
  let scale       = 1000000000
      seconds     = n `div` scale
      nanoseconds = n `mod` scale
   in MkClock seconds nanoseconds

||| Compute difference between two clocks of the same type.
||| @ end the end time
||| @ start the start time
public export
timeDifference : Clock type -> Clock type -> Clock Duration
timeDifference end start = fromNano $ toNano end - toNano start

||| Add a duration to a clock value.
public export
addDuration : {type : ClockType} -> Clock type -> Clock Duration -> Clock type
addDuration clock duration = fromNano $ toNano clock + toNano duration

||| Subtract a duration from a clock value.
public export
subtractDuration : {type : ClockType} -> Clock type -> Clock Duration -> Clock type
subtractDuration clock duration = fromNano $ toNano clock - toNano duration

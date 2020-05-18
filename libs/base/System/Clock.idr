module System.Clock

import PrimIO

||| The various types of system clock available.
public export
data ClockType
  = UTC       -- The time elapsed since the "epoch:" 00:00:00 UTC, January 1, 1970
  | Monotonic -- The time elapsed since some arbitrary point in the past
  | Duration  -- Representing a time duration.
  | Process   -- The amount of CPU time used by the current process.
  | Thread    -- The amount of CPU time used by the current thread.
  | GCCPU     -- The current process's CPU time consumed by the garbage collector.
  | GCReal    -- The current process's real time consumed by the garbage collector.

export
Show ClockType where
  show UTC       = "UTC"
  show Monotonic = "monotonic"
  show Duration  = "duration"
  show Process   = "process"
  show Thread    = "thread"
  show GCCPU     = "gcCPU"
  show GCReal    = "gcReal"

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

||| A helper to deconstruct a Clock.
public export
seconds : Clock type -> Integer
seconds (MkClock s _) = s

||| A helper to deconstruct a Clock.
public export
nanoseconds : Clock type -> Integer
nanoseconds (MkClock _ ns) = ns

||| Make a duration value.
public export
makeDuration : Integer -> Integer -> Clock Duration
makeDuration = MkClock

||| Opaque clock value manipulated by the back-end.
data OSClock : Type where [external]

||| Note: Back-ends are required to implement UTC, monotonic time, CPU time
||| in current process/thread, and time duration; the rest are optional.
data ClockTypeMandatory
  = Mandatory
  | Optional

public export
isClockMandatory : ClockType -> ClockTypeMandatory
isClockMandatory GCCPU  = Optional
isClockMandatory GCReal = Optional
isClockMandatory _      = Mandatory

prim_clockTimeMonotonic : IO OSClock
prim_clockTimeMonotonic = schemeCall OSClock "blodwen-clock-time-monotonic" []

fetchOSClock : ClockType -> IO OSClock
fetchOSClock UTC       = schemeCall OSClock "blodwen-clock-time-utc" []
fetchOSClock Monotonic = prim_clockTimeMonotonic
fetchOSClock Process   = schemeCall OSClock "blodwen-clock-time-process" []
fetchOSClock Thread    = schemeCall OSClock "blodwen-clock-time-thread" []
fetchOSClock GCCPU     = schemeCall OSClock "blodwen-clock-time-gccpu" []
fetchOSClock GCReal    = schemeCall OSClock "blodwen-clock-time-gcreal" []
fetchOSClock Duration  = prim_clockTimeMonotonic

||| A test to determine the status of optional clocks.
osClockValid : OSClock -> IO Int
osClockValid clk = schemeCall Int "blodwen-is-time?" [clk]

fromOSClock : {type : ClockType} -> OSClock -> IO (Clock type)
fromOSClock clk =
  pure $
    MkClock
      {type}
      !(schemeCall Integer "blodwen-clock-second" [clk])
      !(schemeCall Integer "blodwen-clock-nanosecond" [clk])

public export
clockTimeReturnType : (typ : ClockType) -> Type
clockTimeReturnType typ with (isClockMandatory typ)
  clockTimeReturnType typ | Optional = Maybe (Clock typ)
  clockTimeReturnType typ | Mandatory = Clock typ

||| Fetch the system clock of a given kind. If the clock is mandatory,
||| we return a (Clock type) else (Maybe (Clock type)).
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

toNano : Clock type -> Integer
toNano (MkClock seconds nanoseconds) =
  let scale = 1000000000
   in scale * seconds + nanoseconds

fromNano : {type : ClockType} -> Integer -> Clock type
fromNano n =
  let scale       = 1000000000
      seconds     = n `div` scale
      nanoseconds = n `mod` scale
   in MkClock seconds nanoseconds

||| Compute difference between two clocks of the same type.
public export
timeDifference : Clock type -> Clock type -> Clock Duration
timeDifference clock duration = fromNano $ toNano clock - toNano duration

||| Add a duration to a clock value.
public export
addDuration : {type : ClockType} -> Clock type -> Clock Duration -> Clock type
addDuration clock duration = fromNano $ toNano clock + toNano duration

||| Subtract a duration from a clock value.
public export
subtractDuration : {type : ClockType} -> Clock type -> Clock Duration -> Clock type
subtractDuration clock duration = fromNano $ toNano clock - toNano duration

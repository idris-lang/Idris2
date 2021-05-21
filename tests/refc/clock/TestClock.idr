module TestClock

import System.Clock

clockSmall : Clock type -> Bool
clockSmall (MkClock {type} s n) = MkClock {type} s n < MkClock 1 0

clockBig : Clock type -> Bool
clockBig (MkClock {type} s n) = MkClock {type} s n > MkClock 1600000000 0

main : IO ()
main = do
    utc <- clockTime UTC
    monotonicStart <- clockTime Monotonic
    process <- clockTime Process
    thread <- clockTime Thread

    monotonicEnd <- clockTime Monotonic

    putStrLn $ show $ [
        clockBig utc,
        monotonicStart < monotonicEnd,
        clockSmall process,
        clockSmall thread
    ]

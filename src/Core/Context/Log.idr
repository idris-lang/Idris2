module Core.Context.Log

import Core.Context
import Core.Options

import Data.StringMap

import System.Clock

%default covering

-- Log message with a term, translating back to human readable names first
export
logTerm : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          String -> Nat -> Lazy String -> Term vars -> Core ()
logTerm str n msg tm
    = do opts <- getSession
         let lvl = mkLogLevel str n
         if keepLog lvl (logLevel opts)
            then do tm' <- toFullNames tm
                    coreLift $ putStrLn $ "LOG " ++ show lvl ++ ": " ++ msg
                                          ++ ": " ++ show tm'
            else pure ()
export
log' : {auto c : Ref Ctxt Defs} ->
       LogLevel -> Lazy String -> Core ()
log' lvl msg
    = do opts <- getSession
         if keepLog lvl (logLevel opts)
            then coreLift $ putStrLn $ "LOG " ++ show lvl ++ ": " ++ msg
            else pure ()

||| Log a message with the given log level. Use increasingly
||| high log level numbers for more granular logging.
export
log : {auto c : Ref Ctxt Defs} ->
      String -> Nat -> Lazy String -> Core ()
log str n msg
    = do let lvl = mkLogLevel str n
         log' lvl msg

export
logC : {auto c : Ref Ctxt Defs} ->
       String -> Nat -> Core String -> Core ()
logC str n cmsg
    = do opts <- getSession
         let lvl = mkLogLevel str n
         if keepLog lvl (logLevel opts)
            then do msg <- cmsg
                    coreLift $ putStrLn $ "LOG " ++ show lvl ++ ": " ++ msg
            else pure ()

export
logTimeOver : Integer -> Core String -> Core a -> Core a
logTimeOver nsecs str act
    = do clock <- coreLift (clockTime Process)
         let nano = 1000000000
         let t = seconds clock * nano + nanoseconds clock
         res <- act
         clock <- coreLift (clockTime Process)
         let t' = seconds clock * nano + nanoseconds clock
         let time = t' - t
         when (time > nsecs) $
           assert_total $ -- We're not dividing by 0
              do str' <- str
                 coreLift $ putStrLn $ "TIMING " ++ str' ++ ": " ++
                          show (time `div` nano) ++ "." ++
                          addZeros (unpack (show ((time `mod` nano) `div` 1000000))) ++
                          "s"
         pure res
  where
    addZeros : List Char -> String
    addZeros [] = "000"
    addZeros [x] = "00" ++ cast x
    addZeros [x,y] = "0" ++ cast x ++ cast y
    addZeros str = pack str

export
logTimeWhen : {auto c : Ref Ctxt Defs} ->
              Bool -> Lazy String -> Core a -> Core a
logTimeWhen p str act
    = if p
         then do clock <- coreLift (clockTime Process)
                 let nano = 1000000000
                 let t = seconds clock * nano + nanoseconds clock
                 res <- act
                 clock <- coreLift (clockTime Process)
                 let t' = seconds clock * nano + nanoseconds clock
                 let time = t' - t
                 assert_total $ -- We're not dividing by 0
                    coreLift $ putStrLn $ "TIMING " ++ str ++ ": " ++
                             show (time `div` nano) ++ "." ++
                             addZeros (unpack (show ((time `mod` nano) `div` 1000000))) ++
                             "s"
                 pure res
         else act
  where
    addZeros : List Char -> String
    addZeros [] = "000"
    addZeros [x] = "00" ++ cast x
    addZeros [x,y] = "0" ++ cast x ++ cast y
    addZeros str = pack str

logTimeRecord' : {auto c : Ref Ctxt Defs} ->
                 String -> Core a -> Core a
logTimeRecord' key act
    = do clock <- coreLift (clockTime Process)
         let nano = 1000000000
         let t = seconds clock * nano + nanoseconds clock
         res <- act
         clock <- coreLift (clockTime Process)
         let t' = seconds clock * nano + nanoseconds clock
         let time = t' - t
         defs <- get Ctxt
         let tot = case lookup key (timings defs) of
                        Nothing => 0
                        Just (_, t) => t
         put Ctxt (record { timings $= insert key (False, tot + time) } defs)
         pure res

-- for ad-hoc profiling, record the time the action takes and add it
-- to the time for the given category
export
logTimeRecord : {auto c : Ref Ctxt Defs} ->
                String -> Core a -> Core a
logTimeRecord key act
    = do defs <- get Ctxt
         -- Only record if we're not currently recording that key
         case lookup key (timings defs) of
              Just (True, t) => act
              Just (False, t)
                => do put Ctxt (record { timings $= insert key (True, t) } defs)
                      logTimeRecord' key act
              Nothing
                => logTimeRecord' key act

export
showTimeRecord : {auto c : Ref Ctxt Defs} ->
                 Core ()
showTimeRecord
    = do defs <- get Ctxt
         traverse_ showTimeLog (toList (timings defs))
  where
    addZeros : List Char -> String
    addZeros [] = "000"
    addZeros [x] = "00" ++ cast x
    addZeros [x,y] = "0" ++ cast x ++ cast y
    addZeros str = pack str

    showTimeLog : (String, (Bool, Integer)) -> Core ()
    showTimeLog (key, (_, time))
        = do coreLift $ putStr (key ++ ": ")
             let nano = 1000000000
             assert_total $ -- We're not dividing by 0
                    coreLift $ putStrLn $ show (time `div` nano) ++ "." ++
                               addZeros (unpack (show ((time `mod` nano) `div` 1000000))) ++
                               "s"

export
logTime : {auto c : Ref Ctxt Defs} ->
          Lazy String -> Core a -> Core a
logTime str act
    = do opts <- getSession
         logTimeWhen (logTimings opts) str act

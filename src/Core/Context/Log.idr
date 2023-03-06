module Core.Context.Log

import Core.Context
import Core.Options

import Data.String
import Libraries.Data.StringMap

import System.Clock

%default covering

-- if this function is called, then logging must be enabled.
%inline
export
logString : String -> Nat -> String -> Core ()
logString "" n msg = coreLift $ putStrLn
    $ "LOG " ++ show n ++ ": " ++ msg
logString str n msg = coreLift $ putStrLn
    $ "LOG " ++ str ++ ":" ++ show n ++ ": " ++ msg

%inline
export
logString' : LogLevel -> String -> Core ()
logString' lvl =
  logString (fastConcat (intersperse "." (topics lvl)) ++ ":")
            (verbosity lvl)

export
logging' : {auto c : Ref Ctxt Defs} ->
           LogLevel -> Core Bool
logging' lvl = do
    opts <- getSession
    pure $ verbosity lvl == 0 || (logEnabled opts && keepLog lvl (logLevel opts))

export
unverifiedLogging : {auto c : Ref Ctxt Defs} ->
                    String -> Nat -> Core Bool
unverifiedLogging str Z = pure True
unverifiedLogging str n = do
    opts <- getSession
    pure $ logEnabled opts && keepLog (mkUnverifiedLogLevel str n) (logLevel opts)

%inline
export
logging : {auto c : Ref Ctxt Defs} ->
          (s : String) -> {auto 0 _ : KnownTopic s} ->
          Nat -> Core Bool
logging str n = unverifiedLogging str n

||| Log message with a term, translating back to human readable names first.
export
logTerm : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          (s : String) ->
          {auto 0 _ : KnownTopic s} ->
          Nat -> Lazy String -> Term vars -> Core ()
logTerm str n msg tm
    = when !(logging str n)
        $ do tm' <- toFullNames tm
             logString str n $ msg ++ ": " ++ show tm'

export
log' : {auto c : Ref Ctxt Defs} ->
       LogLevel -> Lazy String -> Core ()
log' lvl msg
    = when !(logging' lvl)
        $ logString' lvl msg

||| Log a message with the given log level. Use increasingly
||| high log level numbers for more granular logging.
|||
||| If you want to use some `Core` computation to produce a message string, use `logC`.
||| I.e. instead of `log "topic" 10 "message \{show !(toFullNames fn)}"` use
||| `logC "topic" 10 $ do pure ""message \{show !(toFullNames fn)}""`.
||| This will enfore that additional computation happends only when needed.
||| `do` before `pure` in this case ensures the correct bounds.
export
log : {auto c : Ref Ctxt Defs} ->
      (s : String) ->
      {auto 0 _ : KnownTopic s} ->
      Nat -> Lazy String -> Core ()
log str n msg
    = when !(logging str n)
        $ logString str n msg

export
unverifiedLogC : {auto c : Ref Ctxt Defs} ->
                 (s : String) ->
                 Nat -> Core String -> Core ()
unverifiedLogC str n cmsg
    = when !(unverifiedLogging str n)
        $ do msg <- cmsg
             logString str n msg

%inline
export
logC : {auto c : Ref Ctxt Defs} ->
       (s : String) ->
       {auto 0 _ : KnownTopic s} ->
       Nat -> Core String -> Core ()
logC str = unverifiedLogC str

nano : Integer
nano = 1000000000

micro : Integer
micro = 1000000

export
logTimeOver : Integer -> Core String -> Core a -> Core a
logTimeOver nsecs str act
    = do clock <- coreLift (clockTime Process)
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
                          addZeros (unpack (show ((time `mod` nano) `div` micro))) ++
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
              Bool -> Nat -> Lazy String -> Core a -> Core a
logTimeWhen p lvl str act
    = if p
         then do clock <- coreLift (clockTime Process)
                 let t = seconds clock * nano + nanoseconds clock
                 res <- act
                 clock <- coreLift (clockTime Process)
                 let t' = seconds clock * nano + nanoseconds clock
                 let time = t' - t
                 assert_total $ -- We're not dividing by 0
                    coreLift $ do
                      let header = "TIMING " ++ replicate lvl '+' ++ ifThenElse (0 < lvl) " " ""
                      putStrLn $ header ++ str ++ ": " ++
                             show (time `div` nano) ++ "." ++
                             addZeros (unpack (show ((time `mod` nano) `div` micro))) ++
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
         let t = seconds clock * nano + nanoseconds clock
         res <- act
         clock <- coreLift (clockTime Process)
         let t' = seconds clock * nano + nanoseconds clock
         let time = t' - t
         defs <- get Ctxt
         let tot = case lookup key (timings defs) of
                        Nothing => 0
                        Just (_, t) => t
         put Ctxt ({ timings $= insert key (False, tot + time) } defs)
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
                => do put Ctxt ({ timings $= insert key (True, t) } defs)
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
             assert_total $ -- We're not dividing by 0
                    coreLift $ putStrLn $ show (time `div` nano) ++ "." ++
                               addZeros (unpack (show ((time `mod` nano) `div` micro))) ++
                               "s"

export
logTime : {auto c : Ref Ctxt Defs} ->
          Nat -> Lazy String -> Core a -> Core a
logTime lvl str act
    = do opts <- getSession
         logTimeWhen (maybe False (lvl <=) (logTimings opts)) lvl str act

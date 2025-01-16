module Core.Context.Log

import Core.Context
import Core.Options

import Data.String
import Data.List1
import Libraries.Data.StringMap

import System.Clock

%default covering

padLeft : Nat -> String -> String
padLeft pl str =
    let whitespace = replicate (pl * 2) ' '
    in joinBy "\n" $ toList $ map (\r => whitespace ++ r) $ split (== '\n') str

-- if this function is called, then logging must be enabled.
%inline
export
logString : Nat -> String -> Nat -> String -> Core ()
logString depth "" n msg = coreLift $ putStrLn
    $ padLeft depth $ "LOG " ++ show n ++ ": " ++ msg
logString depth str n msg = coreLift $ putStrLn
    $ padLeft depth $ "LOG " ++ str ++ ":" ++ show n ++ ": " ++ msg

%inline
export
logString' : Nat -> LogLevel -> String -> Core ()
logString' depth lvl =
  logString depth (fastConcat (intersperse "." (topics lvl)) ++ ":")
            (verbosity lvl)

export
getDepth : {auto c : Ref Ctxt Defs} ->
             Core Nat
getDepth
    = do defs <- get Ctxt
         pure (logDepth $ session (options defs))

export
logDepthIncrease : {auto c : Ref Ctxt Defs} -> Core ()
logDepthIncrease
    = do depth <- getDepth
         update Ctxt { options->session->logDepth := depth + 1 }

export
logDepthDecrease : {auto c : Ref Ctxt Defs} -> Core a -> Core a
logDepthDecrease r
    = do r' <- r
         depth <- getDepth
         update Ctxt { options->session->logDepth := depth `minus` 1 }
         pure r'

export
logDepth : {auto c : Ref Ctxt Defs} -> Core a -> Core a
logDepth r
    = do logDepthIncrease
         logDepthDecrease r

export
logQuite : {auto c : Ref Ctxt Defs} -> Core a -> Core a
logQuite r
    = do opts <- getSession
         update Ctxt { options->session->logEnabled := False }
         r' <- r
         update Ctxt { options->session->logEnabled := (logEnabled opts) }
         pure r'

export
logDepthWrap : {auto c : Ref Ctxt Defs} -> (a -> Core b) -> a -> Core b
logDepthWrap fn p
    = do logDepthIncrease
         logDepthDecrease (fn p)

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
          LogTopic -> Nat -> Core Bool
logging s n = unverifiedLogging s.topic n

||| Log message with a term, translating back to human readable names first.
export
logTerm : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          LogTopic -> Nat -> Lazy String -> Term vars -> Core ()
logTerm s n msg tm
    = when !(logging s n)
        $ do depth <- getDepth
             tm' <- toFullNames tm
             logString depth s.topic n $ msg ++ ": " ++ show tm'

export
log' : {auto c : Ref Ctxt Defs} ->
       LogLevel -> Lazy String -> Core ()
log' lvl msg
    = when !(logging' lvl)
        $ do depth <- getDepth
             logString' depth lvl msg

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
      LogTopic -> Nat -> Lazy String -> Core ()
log s n msg
    = when !(logging s n)
        $ do depth <- getDepth
             logString depth s.topic n msg

export
unverifiedLogC : {auto c : Ref Ctxt Defs} ->
                 String -> Nat -> Core String -> Core ()
unverifiedLogC str n cmsg
    = when !(unverifiedLogging str n)
        $ do depth <- getDepth
             msg <- cmsg
             logString depth str n msg

%inline
export
logC : {auto c : Ref Ctxt Defs} ->
       LogTopic -> Nat -> Core String -> Core ()
logC s = unverifiedLogC s.topic

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

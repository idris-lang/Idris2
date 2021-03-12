module Core.Context.Log


import Data.Strings
import Data.These

import Core.Context
import Core.Options
import Data.Maybe
import Data.String
import Data.List
import Data.List1
import Libraries.Data.StringTrie
import Libraries.Data.StringMap

import System.Clock

%default covering

----------------------------------------------------------------------------------
-- TOPICS 
public export
total
splitname : String -> List String 
splitname = List1.forget . Data.String.split (== '.')

public export 
topicList : List (String, String)
topicList = [
    ("", "some documentation of this option"),
    ("auto", "some documentation of this option"),
    ("compile.casetree", "some documentation of this option"),
    ("compiler.inline.eval", "some documentation of this option"),
    ("coverage.empty", "some documentation of this option"),
    ("coverage.recover", "some documentation of this option"),
    ("declare.data", "some documentation of this option"),
    ("declare.data.constructor", "some documentation of this option"),
    ("declare.data.parameters", "some documentation of this option"),
    ("declare.def", "some documentation of this option"),
    ("declare.def.clause", "some documentation of this option"),
    ("declare.def.clause.impossible", "some documentation of this option"),
    ("declare.def.clause.with", "some documentation of this option"),
    ("declare.def.impossible", "some documentation of this option"),
    ("declare.def.lhs", "some documentation of this option"),
    ("declare.param", "some documentation of this option"),
    ("declare.record", "some documentation of this option"),
    ("declare.record.field", "some documentation of this option"),
    ("declare.record.projection", "some documentation of this option"),
    ("declare.type", "some documentation of this option"),
    ("elab", "some documentation of this option"),
    ("elab.ambiguous", "some documentation of this option"),
    ("elab.as", "some documentation of this option"),
    ("elab.case", "some documentation of this option"),
    ("elab.delay", "some documentation of this option"),
    ("elab.hole", "some documentation of this option"),
    ("elab.implementation", "some documentation of this option"),
    ("elab.interface", "some documentation of this option"),
    ("elab.interface.default", "some documentation of this option"),
    ("elab.local", "some documentation of this option"),
    ("elab.prun", "some documentation of this option"),
    ("elab.prune", "some documentation of this option"),
    ("elab.record", "some documentation of this option"),
    ("elab.retry", "some documentation of this option"),
    ("elab.rewrite", "some documentation of this option"),
    ("eval.casetree", "some documentation of this option"),
    ("eval.casetree.stuck", "some documentation of this option"),
    ("eval.eta", "some documentation of this option"),
    ("eval.stuck", "some documentation of this option"),
    ("idemode.hole", "some documentation of this option"),
    ("import", "some documentation of this option"),
    ("interaction.casesplit", "some documentation of this option"),
    ("interaction.generate", "some documentation of this option"),
    ("interaction.search", "some documentation of this option"),
    ("metadata.names", "some documentation of this option"),
    ("quantity", "some documentation of this option"),
    ("quantity.hole", "some documentation of this option"),
    ("specialise", "some documentation of this option"),
    ("totality", "some documentation of this option"),
    ("totality.positivity", "some documentation of this option"),
    ("totality.termination", "some documentation of this option"),
    ("totality.termination.calc", "some documentation of this option"),
    ("totality.termination.guarded", "some documentation of this option"),
    ("totality.termination.sizechange", "some documentation of this option"),
    ("totality.termination.sizechange.checkCall", "some documentation of this option"),
    ("totality.termination.sizechange.checkCall.inPath", "some documentation of this option"),
    ("totality.termination.sizechange.checkCall.inPathNot.restart", "some documentation of this option"),
    ("totality.termination.sizechange.checkCall.inPathNot.return", "some documentation of this option"),
    ("totality.termination.sizechange.inPath", "some documentation of this option"),
    ("totality.termination.sizechange.isTerminating", "some documentation of this option"),
    ("totality.termination.sizechange.needsChecking", "some documentation of this option"),
    ("ttc.write", "some documentation of this option"),
    ("unify.application", "some documentation of this option"),
    ("unify.constant", "some documentation of this option"),
    ("unify.delay", "some documentation of this option"),
    ("unify.equal", "some documentation of this option"),
    ("unify.head", "some documentation of this option"),
    ("unify.instantiate", "some documentation of this option"),
    ("unify.invertible", "some documentation of this option"),
    ("unify.meta", "some documentation of this option"),
    ("unify.noeta", "some documentation of this option"),
    ("unify.postpone", "some documentation of this option"),
    ("unify.retry", "some documentation of this option"),
    ("unify.search", "some documentation of this option"),
    ("unify.unsolved", "some documentation of this option")
] 

public export
total 
possibleTopics : StringTrie String 
possibleTopics = foldr ins StringTrie.empty topicList where 
    ins : (String, String) -> StringTrie String -> StringTrie String
    ins (name, docs) trie = StringTrie.insert (Core.Context.Log.splitname name) docs trie

public export
total 
topicDeclared : String -> Bool 
topicDeclared logctx = isJust $ StringTrie.find (Core.Context.Log.splitname logctx) possibleTopics

-- Log message with a term, translating back to human readable names first
public export
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

public export
total
log' : {auto c : Ref Ctxt Defs} ->
       LogLevel -> Lazy String -> Core ()
log' lvl msg
    = do opts <- getSession
         if keepLog lvl (logLevel opts)
            then coreLift $ putStrLn $ "LOG " ++ show lvl ++ ": " ++ msg
            else pure ()

||| Log a message with the given log level. Use increasingly
||| high log level numbers for more granular logging.
public export
total
log : {auto c : Ref Ctxt Defs} -> (str: String) -> {auto known : (topicDeclared str) = True} 
      -> Nat -> Lazy String -> Core ()
log str n msg
    = do let lvl = mkLogLevel str n
         log' lvl msg

public export
logC : {auto c : Ref Ctxt Defs} ->
       String -> Nat -> Core String -> Core ()
logC str n cmsg
    = do opts <- getSession
         let lvl = mkLogLevel str n
         if keepLog lvl (logLevel opts)
            then do msg <- cmsg
                    coreLift $ putStrLn $ "LOG " ++ show lvl ++ ": " ++ msg
            else pure ()

public export
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

public export
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
public export
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

public export
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

public export
logTime : {auto c : Ref Ctxt Defs} ->
          Lazy String -> Core a -> Core a
logTime str act
    = do opts <- getSession
         logTimeWhen (logTimings opts) str act

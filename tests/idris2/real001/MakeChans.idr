module Main

import Channel
import Linear

data Cmd = Add | Append

Utils : Protocol ()
Utils
    = do cmd <- Request Cmd
         case cmd of
              Add => do Request (Int, Int)
                        Respond Int
                        Done
              Append => do Request (String, String)
                           Respond String
                           Done

utilServer : (1 chan : Server Utils) -> Any IO ()
utilServer chan
    = do cmd @@ chan <- recv chan
         case cmd of
              Add => do (x, y) @@ chan <- recv chan
                        chan <- send chan (x + y)
                        close chan
              Append => do (x, y) @@ chan <- recv chan
                           chan <- send chan (x ++ y)
                           close chan

MakeUtils : Protocol ()
MakeUtils = do cmd <- Request Bool
               if cmd
                  then do Respond (Client Utils); Loop MakeUtils
                  else Done

sendUtils : (1 chan : Server MakeUtils) -> Any IO ()
sendUtils chan
    = do cmd @@ chan <- recv chan
         if cmd
            then do cchan <- Channel.fork utilServer
                    chan <- send chan cchan
                    sendUtils chan
            else close chan

getUtilsChan : (1 chan : Client MakeUtils) ->
               One IO (Client Utils, Client MakeUtils)
getUtilsChan chan
    = do chan <- send chan True
         cchan @@ chan <- recv chan
         pure (cchan, chan)

closeUtilsChan : (1 chan : Client MakeUtils) ->
                 Any IO ()
closeUtilsChan chan
    = do chan <- send chan False
         close chan

doThings : Any IO ()
doThings
    = do -- lift $ printLn "Starting"
         schan <- Channel.fork sendUtils
         res <- getUtilsChan schan
         let (uchan1, schan) = res
         lift $ printLn "Got Chan 1"
         (uchan2, schan) <- getUtilsChan schan
         lift $ printLn "Got Chan 2"
         closeUtilsChan schan

         uchan1 <- send uchan1 Add
         uchan2 <- send uchan2 Append
         uchan2 <- send uchan2 ("aaa", "bbb")
         res @@ uchan2 <- recv uchan2
         close uchan2
         lift $ printLn res

         uchan1 <- send uchan1 (40, 54)
         res @@ uchan1 <- recv uchan1
         close uchan1

         lift $ printLn res

main : IO ()
main = run doThings

module Main

import Channel
import Linear
import System

TestProto : Protocol ()
TestProto
    = do b <- Request Bool
         if b
            then do Respond Char; Done
            else do Respond String; Done

testClient : (1 chan : Client TestProto) -> Any IO ()
testClient chan
    = do lift $ putStrLn "Starting client"
         lift $ sleep 1
         lift $ putStrLn "Sending value"
         chan <- send chan False
         lift $ putStrLn "Sent"
         c @@ chan <- recv chan
         lift $ putStrLn ("Result: " ++ c)
         close chan

testServer : (1 chan : Server TestProto) -> Any IO ()
testServer chan
    = do lift $ putStrLn "Waiting"
         cmd @@ chan <- recv chan
         lift $ putStrLn ("Received " ++ show cmd)
         lift $ sleep 1
         lift $ putStrLn "Sending answer"
         if cmd
            then do chan <- send chan 'a'
                    close chan
            else do chan <- send chan "Foo"
                    close chan

lmain : Any IO ()
lmain
    = do chan <- Channel.fork testServer
         testClient chan

main : IO ()
main = run lmain

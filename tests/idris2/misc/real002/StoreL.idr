module StoreL

import Control.App
import Control.App.Console

data Access = LoggedOut | LoggedIn
data Store : Access -> Type where
     MkStore : (secret : String) -> Store a

interface StoreI e where
  connect : (1 prog : (1 d : Store LoggedOut) ->
            App {l} e ()) -> App {l} e ()
  disconnect : (1 d : Store LoggedOut) -> App {l} e ()

Has [Console] e => StoreI e where
  connect f
      = let (>>=) = bindL in
        let (>>) = seqL in
            do putStrLn "Connected"
               f (MkStore "xyzzy")
  disconnect (MkStore _)
      = do ignore $ putStrLn "Disconnected"

login : (1 s : Store LoggedOut) -> (password : String) ->
        Res Bool (\ok => Store (if ok then LoggedIn else LoggedOut))
login (MkStore secret) password
    = password == "Mornington Crescent" # MkStore secret

logout : (1 s : Store LoggedIn) -> Store LoggedOut
logout (MkStore secret) = MkStore secret

storeProg : Has [Console, StoreI] e => App e ()
storeProg
    = let (>>=) = bindL in
      let (>>) = seqL in
        do putStr "Password: "
           password <- Console.getLine
           connect $ \s =>
             do let True # s = login s password
                       | False # s => do putStrLn "Incorrect password"
                                         disconnect s
                putStrLn "Door opened"
                let s = logout s
                putStrLn "Door closed"
                disconnect s

foo : IO ()
foo = run storeProg

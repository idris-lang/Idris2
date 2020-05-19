module Store

import Control.App
import Control.App.Console

data Access = LoggedOut | LoggedIn
data Store : Access -> Type where
     MkStore : (secret : String) -> Store a

interface StoreI e where
  connect : App1 e (Store LoggedOut)
  login : (1 d : Store LoggedOut) -> (password : String) ->
          App1 e (Res Bool (\ok => Store (if ok then LoggedIn else LoggedOut)))
  logout : (1 d : Store LoggedIn) -> App1 e (Store LoggedOut)
  readSecret : (1 d : Store LoggedIn) -> 
               App1 e (Res String (const (Store LoggedIn)))
  disconnect : (1 d : Store LoggedOut) -> App {l} e ()

Has [Console] e => StoreI e where
  connect
      = do app $ putStrLn "Connect"
           pure1 (MkStore "xyzzy")

  login (MkStore str) pwd
      = if pwd == "Mornington Crescent"
           then pure1 (True @@ MkStore str)
           else pure1 (False @@ MkStore str)
  logout (MkStore str) = pure1 (MkStore str)
  readSecret (MkStore str) = pure1 (str @@ MkStore str)

  disconnect (MkStore _)
      = putStrLn "Door destroyed"

storeProg : Has [Console, StoreI] e => 
            App e ()
storeProg
    = app1 $ do
         s <- connect
         app $ putStr "Password: "
         pwd <- app $ getStr
         True @@ s <- login s pwd
              | False @@ s => do app $ putStrLn "Login failed"
                                 app $ disconnect s
         app $ putStrLn "Logged in"
         secret @@ s <- readSecret s
         app $ putStrLn ("Secret: " ++ secret)
         s <- logout s 
         app $ putStrLn "Logged out"
         app $ disconnect s

main : IO ()
main = run storeProg

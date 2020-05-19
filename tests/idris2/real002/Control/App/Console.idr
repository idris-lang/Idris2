module Control.App.Console

import public Control.App

public export
interface Console e where
  putStr : String -> App {l} e ()
  getStr : App {l} e String

export 
PrimIO e => Console e where
  putStr str = primIO $ putStr str
  getStr = primIO $ getLine

export
putStrLn : Console e => String -> App {l} e ()
putStrLn str = putStr (str ++ "\n")

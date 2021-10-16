module Control.App.Console

import public Control.App

%default total

public export
interface Console e where
  putChar : Char -> App {l} e ()
  putStr : String -> App {l} e ()
  getChar : App {l} e Char
  getLine : App {l} e String

export
PrimIO e => Console e where
  putChar c = primIO $ putChar c
  putStr str = primIO $ putStr str
  getChar = primIO getChar
  getLine = primIO getLine

export
putStrLn : Console e => String -> App {l} e ()
putStrLn str = putStr (str ++ "\n")

export
putCharLn : Console e => Char -> App {l} e ()
putCharLn c = putStrLn $ strCons c ""

export
print : Show a => Console e => a -> App {l} e ()
print x = putStr $ show x

export
printLn : Show a => Console e => a -> App {l} e ()
printLn x = putStrLn $ show x

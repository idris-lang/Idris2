module Main

import Data.List
import Data.Stream
import System

-- Reports each evaluation of a constant's body.
traced : String -> a -> a
traced msg x = unsafePerformIO (do putStrLn ("  [eval " ++ msg ++ "]"); pure x)

-- 1. computed, never used: must not be evaluated at all
unused : Nat
unused = traced "unused" (length (replicate 1000 'x'))

-- 2. computed, used twice: evaluated once, at the first use
shared : Nat
shared = traced "shared" (sum [1 .. 100])

-- 3. reaches a crash (`hd` is partial), used twice: evaluated once
partial
hd : List Nat -> Nat
hd (x :: _) = x
hd [] = idris_crash "hd of empty"

partial
viaPartial : Nat
viaPartial = traced "viaPartial" (hd [7, 8, 9])

-- 4. crashes, never used
partial
crashes : Nat
crashes = hd []

-- 5. a value: constructors, a closure, a reference to another value
pair : (Nat, Nat -> Nat)
pair = (3, (+ 1))

nested : List (Nat, Nat -> Nat)
nested = [pair, pair]

-- 6. a constant that depends on another computed constant
dependent : Nat
dependent = traced "dependent" (shared + 1)

-- 7. recursive constants
ones : Stream Nat
ones = 1 :: ones

mutual
  evens : Stream Nat
  evens = 0 :: odds
  odds : Stream Nat
  odds = 1 :: evens

-- 8. a Lazy constant, used twice and passed on unforced
lazyC : Lazy Nat
lazyC = traced "lazyC" (sum [1 .. 10])

useLazy : Lazy Nat -> Nat
useLazy x = x + x

-- 9. a constant holding a function built by a computation
adder : Nat -> Nat
adder = traced "adder" (\x => x + shared)

-- 10. a Lazy constant used twice in a branch that is not taken: the shared
--     subexpression that forces it must not be evaluated either
lazyUnused : Lazy Nat
lazyUnused = traced "lazyUnused" (sum [1 .. 20])

-- 11. a Lazy constant that can reach a crash and whose body is a `let`,
--     stored unforced in a record
record Entry where
  constructor MkEntry
  name : String
  text : Lazy (Either String String)

partial
viaLet : Lazy String
viaLet = let h = hd [7, 8] in traced "viaLet" (show h ++ "!")

partial
entry : Entry
entry = MkEntry "entry" (Right viaLet)

partial
main : IO ()
main = do
  putStrLn "main starts"
  args <- getArgs
  when (length args > 5) $ do   -- never true: keeps the unused ones alive
    printLn unused
    printLn crashes
    printLn lazyUnused
    printLn lazyUnused
  putStrLn "shared:";     printLn shared;     printLn shared
  putStrLn "viaPartial:"; printLn viaPartial; printLn viaPartial
  putStrLn "nested:";     printLn (map (\p => snd p (fst p)) nested)
  putStrLn "dependent:";  printLn dependent;  printLn dependent
  putStrLn "streams:";    printLn (take 3 ones); printLn (take 4 evens)
  putStrLn "lazyC:";      printLn (force lazyC + lazyC); printLn (useLazy lazyC)
  putStrLn "adder:";      printLn (adder 1);  printLn (adder 2)
  putStrLn "entry:";      putStrLn (entry.name ++ ": " ++ either id id entry.text)
  putStrLn "done"

module Specifiers

{- This tests both the given specifiers and the error reporting of them.
   To this end it tests via:
   -o foo           -- testing cli compilation
   --exec main      -- testing cli execution

   > :exec main     -- testing repl execution

   > :set eval exec -- testing repl evaluation with eval set to execute
   > main
-}

-- Generic match good for any scheme backend
%foreign "scheme:+"
plusGeneric : Int -> Int -> Int

-- We're testing with --cg chez so this specifier should be chosen.
%foreign "scheme,chez:+"
plusChez : Int -> Int -> Int

-- We're testing with --cg chez so this should match C because chez accepts C
-- specifiers but the next test should fail.
%foreign "scheme,racket:+"
         "C:notreal,notalib"
plusRacketOK : Int -> Int -> Int

-- We're testing with --cg chez so this shouldn't find a valid specifier to use.
%foreign "scheme,racket:+"
plusRacketFail : Int -> Int -> Int

-- We don't actually do any printing this is just to use the specifiers so the
-- failures are exposed.
main : IO ()
main = do
  printLn $ plusGeneric 2 3
  printLn $ plusChez 2 3
  printLn $ plusRacketOK 2 3
  printLn $ plusRacketFail 2 3
  pure ()

module System.REPL

import System.File

%default covering

||| A basic read-eval-print loop, maintaining a state
|||
||| @ state   the input state
||| @ prompt  the prompt to show
||| @ onInput the function to run on reading input, returning a String to
|||           output and a new state. Returns Nothing if the repl should exit
export
replWith : HasIO io =>
           (state : a) -> (prompt : String) ->
           (onInput : a -> String -> Maybe (String, a)) -> io ()
replWith acc prompt fn
   = do eof <- fEOF stdin
        if eof
          then pure ()
          else do putStr prompt
                  fflush stdout
                  x <- getLine
                  case fn acc x of
                       Just (out, acc') =>
                           do putStr out
                              replWith acc' prompt fn
                       Nothing => pure ()

||| A basic read-eval-print loop
|||
||| @ prompt  the prompt to show
||| @ onInput the function to run on reading input, returning a String to
|||           output
export
repl : HasIO io =>
       (prompt : String) -> (onInput : String -> String) -> io ()
repl prompt fn
   = replWith () prompt (\x, s => Just (fn s, ()))

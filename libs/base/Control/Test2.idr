import Control.App2

namespace Console
  public export
  interface Console e where
    putStr : String -> App e ()
    getStr : App e String

  export
  PrimIO e => Console e where
    putStr str = primIO $ putStr str
    getStr = primIO $ getLine

  export
  putStrLn : Console e => String -> App e ()
  putStrLn str = putStr (str ++ "\n")

namespace StateEx
  public export
  interface Console e => StateEx e where
    inc : App e Int
    testRes : String -> App e Bool

  export
  Has [Console, State Int, Exception String] e => StateEx e where
    inc
        = do count <- get
             put (count + the Int 1)
             pure count

    testRes str
        = do count <- get
             case str of
                  "DONE" => pure True
                  "BAD" => throw "Nope"
                  _ => do putStrLn $ "Hello " ++ str ++ " " ++ show count
                          pure False

test : Has [StateEx] e => App e ()
test
    = do putStr "Name: "
         inc
         x <- getStr
         done <- testRes x
         if done
            then pure ()
            else test

addState : Has [Console, StateEx] e => App e ()
addState
    = do new "foo" $
             do putStrLn "Here we go!"
                str <- get
                putStrLn str

runTest : IO ()
runTest
    = run $ do new (the Int 0) $
               handle (do test; addState) pure
                      (\err : String =>
                              putStrLn $ "Error: " ++ err)

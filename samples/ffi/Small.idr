libsmall : String -> String
libsmall fn = "C:" ++ fn ++ ",libsmallc"

%foreign (libsmall "add")
add : Int -> Int -> Int

%foreign (libsmall "addWithMessage")
prim__addWithMessage : String -> Int -> Int -> PrimIO Int

addWithMessage : String -> Int -> Int -> IO Int
addWithMessage s x y = primIO $ prim__addWithMessage s x y

%foreign (libsmall "applyFn")
prim__applyFn : String -> Int -> (String -> Int -> String) -> PrimIO String

applyFn : String -> Int -> (String -> Int -> String) -> IO String
applyFn c i f = primIO $ prim__applyFn c i f

%foreign (libsmall "applyFn")
prim__applyFnIO : String -> Int -> (String -> Int -> PrimIO String) -> PrimIO String

applyFnIO : String -> Int -> (String -> Int -> IO String) -> IO String
applyFnIO c i f = primIO $ prim__applyFnIO c i (\s, i => toPrim $ f s i)

pluralise : String -> Int -> IO String
pluralise str x
    = do putStrLn "Pluralising"
         pure $ show x ++ " " ++
                if x == 1
                   then str
                   else str ++ "s"

main : IO ()
main
    = do -- printLn (add 70 24)
         -- primIO $ prim__addWithMessage "Sum" 70 24
         str1 <- applyFnIO "Biscuit" 10 pluralise
         putStrLn str1
         str2 <- applyFnIO "Tree" 1 pluralise
         putStrLn str2

%foreign "C:mkThing, libmkalloc"
prim__mkThing : PrimIO AnyPtr
%foreign "C:getStr, libmkalloc"
prim__getStr : GCAnyPtr -> PrimIO String
%foreign "C:freeThing, libmkalloc"
prim__freeThing : AnyPtr -> PrimIO ()

mkThing : IO AnyPtr
mkThing = primIO prim__mkThing

getThingStr : GCAnyPtr -> IO String
getThingStr t = primIO (prim__getStr t)

freeThing : AnyPtr -> IO ()
freeThing t = primIO (prim__freeThing t)

doThings : IO ()
doThings
     = do xp <- mkThing
          yp <- mkThing

          x <- onCollectAny xp (\p => do putStrLn "Free X"
                                         freeThing p)
          y <- onCollectAny yp (\p => do putStrLn "Free Y"
                                         freeThing p)

          putStrLn !(getThingStr x)
          putStrLn !(getThingStr y)

main : IO ()
main = do doThings
          putStrLn "Done"

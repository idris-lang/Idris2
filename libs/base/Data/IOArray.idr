module Data.IOArray

import Data.List

-- Implemented externally
data ArrayData : Type -> Type where

-- 'unsafe' primitive access, backend dependent
-- get and set assume that the bounds have been checked. Behavious is undefined
-- otherwise.
%extern prim__newArray : forall a . Int -> a -> PrimIO (ArrayData a)
%extern prim__arrayGet : forall a . ArrayData a -> Int -> PrimIO a
%extern prim__arraySet : forall a . ArrayData a -> Int -> a -> PrimIO ()

export
record IOArray elem where
  constructor MkIOArray
  max : Int
  content : ArrayData (Maybe elem)

export
newArray : Int -> IO (IOArray elem)
newArray size
    = pure (MkIOArray size !(primIO (prim__newArray size Nothing)))

export
writeArray : IOArray elem -> Int -> elem -> IO ()
writeArray arr pos el
    = if pos < 0 || pos >= max arr
         then pure ()
         else primIO (prim__arraySet (content arr) pos (Just el))

export
readArray : IOArray elem -> Int -> IO (Maybe elem)
readArray arr pos
    = if pos < 0 || pos >= max arr
         then pure Nothing
         else primIO (prim__arrayGet (content arr) pos)

-- Make a new array of the given size with the elements copied from the
-- other array
export
newArrayCopy : (newsize : Int) -> IOArray elem -> IO (IOArray elem)
newArrayCopy newsize arr
    = do let newsize' = if newsize < max arr then max arr else newsize
         arr' <- newArray newsize'
         copyFrom (content arr) (content arr') (max arr - 1)
         pure arr'
  where
    copyFrom : ArrayData (Maybe elem) ->
               ArrayData (Maybe elem) ->
               Int -> IO ()
    copyFrom old new pos
        = if pos < 0
             then pure ()
             else do el <- primIO $ prim__arrayGet old pos
                     primIO $ prim__arraySet new pos el
                     assert_total (copyFrom old new (pos - 1))

export
toList : IOArray elem -> IO (List (Maybe elem))
toList arr = iter 0 (max arr) []
  where
    iter : Int -> Int -> List (Maybe elem) -> IO (List (Maybe elem))
    iter pos end acc
         = if pos >= end
              then pure (reverse acc)
              else do el <- readArray arr pos
                      assert_total (iter (pos + 1) end (el :: acc))

export
fromList : List (Maybe elem) -> IO (IOArray elem)
fromList ns
    = do arr <- newArray (cast (length ns))
         addToArray 0 ns arr
         pure arr
  where
    addToArray : Int -> List (Maybe elem) -> IOArray elem -> IO ()
    addToArray loc [] arr = pure ()
    addToArray loc (Nothing :: ns) arr
        = assert_total (addToArray (loc + 1) ns arr)
    addToArray loc (Just el :: ns) arr
        = do primIO $ prim__arraySet (content arr) loc (Just el)
             assert_total (addToArray (loc + 1) ns arr)

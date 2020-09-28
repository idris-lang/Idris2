module Data.IOArray

import Data.IOArray.Prims
import Data.List

export
record IOArray elt where
  constructor MkIOArray
  maxSize : Int
  content : ArrayData (Maybe elt)

export
max : IOArray elt -> Int
max = maxSize

export
newArray : HasIO io => Int -> io (IOArray elt)
newArray size
    = pure (MkIOArray size !(primIO (prim__newArray size Nothing)))

export
writeArray : HasIO io => IOArray elt -> Int -> elt -> io ()
writeArray arr pos el
    = if pos < 0 || pos >= max arr
         then pure ()
         else primIO (prim__arraySet (content arr) pos (Just el))

export
readArray : HasIO io => IOArray elt -> Int -> io (Maybe elt)
readArray arr pos
    = if pos < 0 || pos >= max arr
         then pure Nothing
         else primIO (prim__arrayGet (content arr) pos)

-- Make a new array of the given size with the elements copied from the
-- other array
export
newArrayCopy : HasIO io =>
               (newsize : Int) -> IOArray elt -> io (IOArray elt)
newArrayCopy newsize arr
    = do let newsize' = if newsize < max arr then max arr else newsize
         arr' <- newArray newsize'
         copyFrom (content arr) (content arr') (max arr - 1)
         pure arr'
  where
    copyFrom : ArrayData (Maybe elt) ->
               ArrayData (Maybe elt) ->
               Int -> io ()
    copyFrom old new pos
        = if pos < 0
             then pure ()
             else do el <- primIO $ prim__arrayGet old pos
                     primIO $ prim__arraySet new pos el
                     assert_total (copyFrom old new (pos - 1))

export
toList : HasIO io => IOArray elt -> io (List (Maybe elt))
toList arr = iter 0 (max arr) []
  where
    iter : Int -> Int -> List (Maybe elt) -> io (List (Maybe elt))
    iter pos end acc
         = if pos >= end
              then pure (reverse acc)
              else do el <- readArray arr pos
                      assert_total (iter (pos + 1) end (el :: acc))

export
fromList : List (Maybe elt) -> IO (IOArray elt)
fromList ns
    = do arr <- newArray (cast (length ns))
         addToArray 0 ns arr
         pure arr
  where
    addToArray : Int -> List (Maybe elt) -> IOArray elt -> IO ()
    addToArray loc [] arr = pure ()
    addToArray loc (Nothing :: ns) arr
        = assert_total (addToArray (loc + 1) ns arr)
    addToArray loc (Just el :: ns) arr
        = do primIO $ prim__arraySet (content arr) loc (Just el)
             assert_total (addToArray (loc + 1) ns arr)

module Main

import Data.Buffer
import Data.List.Quantifiers
import Data.String

import System
import System.File

%default total

data AType
  = ABool
  | ABits8
  | ABits16
  | ABits32
  | ABits64
  | AnInt8
  | AnInt16
  | AnInt32
  | AnInt64
  | ANat
  | AnInteger
  | AString
  | ADouble
  -- hack
  | ANewline

Val : AType -> Type
Val ABool = Bool
Val ABits8 = Bits8
Val ABits16 = Bits16
Val ABits32 = Bits32
Val ABits64 = Bits64
Val AnInt8 = Int8
Val AnInt16 = Int16
Val AnInt32 = Int32
Val AnInt64 = Int64
Val ANat = Nat
Val AnInteger = Integer
Val AString = String
Val ADouble = Double
Val ANewline = ()

eqAType : (d : AType) -> Val d -> Val d -> Bool
eqAType ABool = (==)
eqAType ABits8 = (==)
eqAType ABits16 = (==)
eqAType ABits32 = (==)
eqAType ABits64 = (==)
eqAType AnInt8 = (==)
eqAType AnInt16 = (==)
eqAType AnInt32 = (==)
eqAType AnInt64 = (==)
eqAType ANat = (==)
eqAType AnInteger = (==)
eqAType AString = (==)
eqAType ADouble = (==)
eqAType ANewline = (==)

eqAll : {ds : List AType} -> All Val ds -> All Val ds -> Bool
eqAll [] [] = True
eqAll (v :: vs) (w :: ws) = eqAType _ v w && eqAll vs ws

showAType : (d : AType) -> Val d -> String
showAType ABool = show
showAType ABits8 = show
showAType ABits16 = show
showAType ABits32 = show
showAType ABits64 = show
showAType AnInt8 = show
showAType AnInt16 = show
showAType AnInt32 = show
showAType AnInt64 = show
showAType ANat = show
showAType AnInteger = show
showAType AString = show
showAType ADouble = show
showAType ANewline = const "()\n"

showAll : {ds : List AType} -> All Val ds -> String
showAll vs = "[ " ++ joinBy ", " (go vs) ++ "]" where

  go : {ds : List AType} -> All Val ds -> List String
  go [] = []
  go (v :: vs) = showAType _ v :: go vs

example : All Val [ ABool, ANewline
                  , ABits8, ABits16, ABits32, ABits64, ANewline
                  , AnInt8, AnInt16, AnInt32, AnInt64, ANewline
                  , AnInt8, AnInt16, AnInt32, AnInt64, ANewline
                  , ANat, ANat, AnInteger, AnInteger, ANewline
                  , AString, AString, ANewline
                  , ADouble, ADouble, ANewline
                  ]
example = [ True, ()
          , 255, 65535, 4294967295, 18446744073709551615, ()
          , 127, 32767, 2147483647, 9223372036854775807, ()
          , -127, -32767, -2147483647, -9223372036854775807, ()
          , 0, 28446744073709551615, 28446744073709551615, -28446744073709551615, ()
          , "hello world", "", ()
          , 1.0, -100.00009, ()
          ]

||| Returns the end offset
setAType : (d : AType) -> (buf : Buffer) -> (offset : Int) -> Val d -> IO Int
setAType ABool buf offset v = offset + 1 <$ setBool buf offset v
setAType ABits8 buf offset v = offset + 1 <$ setBits8 buf offset v
setAType ABits16 buf offset v = offset + 2 <$ setBits16 buf offset v
setAType ABits32 buf offset v = offset + 4 <$ setBits32 buf offset v
setAType ABits64 buf offset v = offset + 8 <$ setBits64 buf offset v
setAType AnInt8 buf offset v = offset + 1 <$ setInt8 buf offset v
setAType AnInt16 buf offset v = offset + 2 <$ setInt16 buf offset v
setAType AnInt32 buf offset v = offset + 4 <$ setInt32 buf offset v
setAType AnInt64 buf offset v = offset + 8 <$ setInt64 buf offset v
setAType ANat buf offset v = setNat buf offset v
setAType AnInteger buf offset v = setInteger buf offset v
setAType AString buf offset v = do
  let len = stringByteLength v
  setInt64 buf offset (cast len)
  setString buf (offset + 8) v
  pure (offset + 8 + len)
setAType ADouble buf offset v = offset + 8 <$ setDouble buf offset v
setAType ANewline buf offset v = pure offset

setATypes : {ds : List AType} -> (buf : Buffer) -> (offset : Int) -> All Val ds -> IO Int
setATypes buf offset [] = pure offset
setATypes buf offset (v :: vs)
  = do end <- setAType _ buf offset v
       setATypes buf end vs

getAType : (d : AType) -> (buf : Buffer) -> (offset : Int) -> IO (Int, Val d)
getAType ABool buf offset = (offset + 1,) <$> getBool buf offset
getAType ABits8 buf offset = (offset + 1,) <$> getBits8 buf offset
getAType ABits16 buf offset = (offset + 2,) <$> getBits16 buf offset
getAType ABits32 buf offset = (offset + 4,) <$> getBits32 buf offset
getAType ABits64 buf offset = (offset + 8,) <$> getBits64 buf offset
getAType AnInt8 buf offset = (offset + 1,) <$> getInt8 buf offset
getAType AnInt16 buf offset = (offset + 2,) <$> getInt16 buf offset
getAType AnInt32 buf offset = (offset + 4,) <$> getInt32 buf offset
getAType AnInt64 buf offset = (offset + 8,) <$> getInt64 buf offset
getAType ANat buf offset = getNat buf offset
getAType AnInteger buf offset = getInteger buf offset
getAType AString buf offset
  = do len <- cast <$> getInt64 buf offset
       str <- getString buf (offset + 8) len
       pure (offset + 8 + len, str)
getAType ADouble buf offset = (offset + 8,) <$> getDouble buf offset
getAType ANewline buf offset = pure (offset, ())

getATypes : (ds : List AType) -> (buf : Buffer) -> (offset : Int) -> IO (All Val ds)
getATypes [] buf offset = pure []
getATypes (d :: ds) buf offset
   = do (end, v) <- getAType d buf offset
        (v ::) <$> getATypes ds buf end



failWith : String -> IO a
failWith msg
  = do Right () <- fPutStrLn stderr msg
         | _ => exitFailure
       exitFailure

main : IO ()
main = do
  putStrLn (showAll example)

  -- serialise
  Just buf <- newBuffer 10000
      | Nothing => failWith "Couldn't allocate buffer"
  size <- setATypes buf 0 example
  Right () <- writeBufferToFile "tmp.bin" buf size
      | Left (err, _) => failWith (show err)

  -- deserialise
  Right buf <- createBufferFromFile "tmp.bin"
      | Left err => failWith (show err)

  example' <- getATypes _ buf 0

  -- check that (deserialise . serialise) is the identity
  let True = eqAll example example'
    | False => failWith
             """
             Roundtrip failed!
             Serialised:
             \{showAll example}

             Deserialised:
             \{showAll example'}
             """

  putStrLn "Roundtrip succeeded!"

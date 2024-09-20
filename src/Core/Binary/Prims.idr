module Core.Binary.Prims

import Core.Context.Context
import Core.Core

import Data.Buffer
import Data.List
import Data.List.Elem
import Data.List1
import Data.SnocList
import Data.Nat
import Data.String
import Data.Vect

import Libraries.Data.PosMap
import public Libraries.Utils.Binary
import public Libraries.Utils.String
import Libraries.Data.WithDefault

import System.Info
import System.File

-- A label for binary states
export
data Bin : Type where

-- A label for storing resolved name ids
export
data ResID : Type where

public export
interface TTC a where -- TTC = TT intermediate code/interface file
  -- Add binary data representing the value to the given buffer
  toBuf : Ref Bin Binary -> a -> Core ()
  -- Return the data representing a thing of type 'a' from the given buffer.
  -- Throws if the data can't be parsed as an 'a'
  fromBuf : Ref Bin Binary -> Core a

-- Create a new list of chunks, initialised with one 64k chunk
export
initBinary : Core (Ref Bin Binary)
initBinary
    = do Just buf <- coreLift $ newBuffer blockSize
             | Nothing => throw (InternalError "Buffer creation failed")
         newRef Bin (newBinary buf (cast blockSize))

export
initBinaryS : Int -> Core (Ref Bin Binary)
initBinaryS s
    = do Just buf <- coreLift $ newBuffer s
             | Nothing => throw (InternalError "Buffer creation failed")
         newRef Bin (newBinary buf (cast s))

extendBinary : Integer -> Binary -> Core Binary
extendBinary need (MkBin buf l s u)
    = do let newsize = s * 2
         let s' = if (newsize - l) < need
                     then newsize + need
                     else newsize
         Just buf' <- coreLift $ resizeBuffer buf (cast s')
             | Nothing => throw (InternalError "Buffer expansion failed")
         pure (MkBin buf' l s' u)

export
corrupt : String -> Core a
corrupt ty = throw (TTCError (Corrupt ty))

-- tag and getTag assume the Int is in the range 0-255 (we don't have
-- Bits8 yet!)
export
tag : {auto b : Ref Bin Binary} -> Int -> Core ()
tag {b} val
    = do chunk <- get Bin
         if avail chunk >= 1
            then
              do coreLift $ setBits8 (buf chunk) (cast $ loc chunk) $ cast val
                 put Bin (appended 1 chunk)
            else do chunk' <- extendBinary 1 chunk
                    coreLift $ setBits8 (buf chunk') (cast $ loc chunk') $ cast val
                    put Bin (appended 1 chunk')

export
getTag : {auto b : Ref Bin Binary} -> Core Int
getTag {b}
    = do chunk <- get Bin
         if toRead chunk >= 1
            then
              do val <- coreLift $ getBits8 (buf chunk) (cast $ loc chunk)
                 put Bin (incLoc 1 chunk)
                 pure $ cast val
              else throw (TTCError (EndOfBuffer "Bits8"))

-- Primitives; these are the only things that have to deal with growing
-- the buffer list

-- Some useful types from the prelude

export
[Wasteful] TTC Int where
  toBuf b val
    = do chunk <- get Bin
         if avail chunk >= 8
            then
              do coreLift $ setInt (buf chunk) (cast $ loc chunk) val
                 put Bin (appended 8 chunk)
            else do chunk' <- extendBinary 8 chunk
                    coreLift $ setInt (buf chunk') (cast $ loc chunk') val
                    put Bin (appended 8 chunk')

  fromBuf b
    = do chunk <- get Bin
         if toRead chunk >= 8
            then
              do val <- coreLift $ getInt (buf chunk) (cast $ loc chunk)
                 put Bin (incLoc 8 chunk)
                 pure val
              else throw (TTCError (EndOfBuffer ("Int " ++ show (loc chunk, size chunk))))

export
TTC Int where
  toBuf b val
    = if val >= -127 && val < 128
         then tag (val + 127)
         else do tag 255
                 chunk <- get Bin
                 if avail chunk >= 8
                    then
                      do coreLift $ setInt (buf chunk) (cast $ loc chunk) val
                         put Bin (appended 8 chunk)
                    else do chunk' <- extendBinary 8 chunk
                            coreLift $ setInt (buf chunk') (cast $ loc chunk') val
                            put Bin (appended 8 chunk')

  fromBuf b
    = case !getTag of
           255 => do chunk <- get Bin
                     if toRead chunk >= 8
                       then
                         do val <- coreLift $ getInt (buf chunk) (cast $ loc chunk)
                            put Bin (incLoc 8 chunk)
                            pure val
                       else throw (TTCError (EndOfBuffer ("Int " ++ show (loc chunk, size chunk))))
           t => pure (t - 127)

export
TTC String where
  toBuf b val
      -- To support UTF-8 strings, this has to get the length of the string
      -- in bytes, not the length in characters.
      = do let ireq = stringByteLength val
           let req : Integer = cast ireq
           toBuf b ireq
           chunk <- get Bin
           if avail chunk >= req
              then
                do coreLift $ setString (buf chunk) (cast $ loc chunk) val
                   put Bin (appended req chunk)
              else do chunk' <- extendBinary req chunk
                      coreLift $ setString (buf chunk') (cast $ loc chunk') val
                      put Bin (appended req chunk')

  fromBuf b
      = do ilen <- fromBuf {a = Int} b
           chunk <- get Bin
           let len = cast ilen
           when (len < 0) $ corrupt "String"
           if toRead chunk >= len
              then
                do val <- coreLift $ getString (buf chunk) (cast $ loc chunk) ilen
                   put Bin (incLoc len chunk)
                   pure val
              else throw (TTCError (EndOfBuffer ("String length " ++ show len ++
                                                 " at " ++ show (loc chunk))))

export
TTC Binary where
  toBuf b val
    = do let len = used val
         let ilen : Int = cast len
         toBuf b ilen
         chunk <- get Bin
         if avail chunk >= len
            then
              do coreLift $ copyData (buf val) 0 ilen
                                     (buf chunk) (cast $ loc chunk)
                 put Bin (appended len chunk)
            else do chunk' <- extendBinary len chunk
                    coreLift $ copyData (buf val) 0 ilen
                                        (buf chunk') (cast $ loc chunk')
                    put Bin (appended len chunk')

  fromBuf b
    = do ilen <- fromBuf b
         let len : Integer = cast ilen
         chunk <- get Bin
         if toRead chunk >= len
            then
              do Just newbuf <- coreLift $ newBuffer ilen
                      | Nothing => corrupt "Binary"
                 coreLift $ copyData (buf chunk) (cast $ loc chunk) ilen
                                     newbuf 0
                 put Bin (incLoc len chunk)
                 pure (MkBin newbuf 0 len len)
            else throw (TTCError (EndOfBuffer "Binary"))

export
TTC Bool where
  toBuf b False = tag 0
  toBuf b True = tag 1
  fromBuf b
      = case !getTag of
             0 => pure False
             1 => pure True
             _ => corrupt "Bool"

export
TTC Char where
  toBuf b c = toBuf b (cast {to=Int} c)
  fromBuf b
      = do i <- fromBuf b
           pure (cast {from=Int} i)

export
TTC Double where
  toBuf b val
    = do chunk <- get Bin
         if avail chunk >= 8
            then
              do coreLift $ setDouble (buf chunk) (cast $ loc chunk) val
                 put Bin (appended 8 chunk)
            else do chunk' <- extendBinary 8 chunk
                    coreLift $ setDouble (buf chunk') (cast $ loc chunk') val
                    put Bin (appended 8 chunk')

  fromBuf b
    = do chunk <- get Bin
         if toRead chunk >= 8
            then
              do val <- coreLift $ getDouble (buf chunk) (cast $ loc chunk)
                 put Bin (incLoc 8 chunk)
                 pure val
              else throw (TTCError (EndOfBuffer "Double"))

export
(TTC a, TTC b) => TTC (a, b) where
  toBuf b (x, y)
     = do toBuf b x
          toBuf b y
  fromBuf b
     = do x <- fromBuf b
          y <- fromBuf b
          pure (x, y)

export
TTC () where
  toBuf b () = pure ()
  fromBuf b = pure ()

export
(TTC a, {y : a} -> TTC (p y)) => TTC (DPair a p) where
  toBuf b (vs ** tm)
      = do toBuf b vs
           toBuf b tm

  fromBuf b
      = do x <- fromBuf b
           p <- fromBuf b
           pure (x ** p)

export
TTC a => TTC (Maybe a) where
  toBuf b Nothing
     = tag 0
  toBuf b (Just val)
     = do tag 1
          toBuf b val

  fromBuf b
     = case !getTag of
            0 => pure Nothing
            1 => do val <- fromBuf b
                    pure (Just val)
            _ => corrupt "Maybe"

export
TTC a => TTC (WithDefault a def) where
  toBuf b def = onWithDefault
                  (tag 0)
                  (\v => do tag 1
                            toBuf b v)
                  def

  fromBuf b
     = case !getTag of
            0 => pure defaulted
            1 => do val <- fromBuf b
                    pure (specified val)
            _ => corrupt "WithDefault"

export
(TTC a, TTC b) => TTC (Either a b) where
  toBuf b (Left val)
     = do tag 0
          toBuf b val
  toBuf b (Right val)
     = do tag 1
          toBuf b val

  fromBuf b
     = case !getTag of
            0 => do val <- fromBuf b
                    pure (Left val)
            1 => do val <- fromBuf b
                    pure (Right val)
            _ => corrupt "Either"

export
TTC a => TTC (List a) where
  toBuf b xs
      = do toBuf b (TailRec_length xs)
           traverse_ (toBuf b) xs
    where
      ||| Tail-recursive length as buffer sizes can get large
      |||
      ||| Once we port to Idris2, can use Data.List.TailRec.length instead
      length_aux : List a -> Int -> Int
      length_aux [] len = len
      length_aux (_::xs) len = length_aux xs (1 + len)

      TailRec_length : List a -> Int
      TailRec_length xs = length_aux xs 0

  fromBuf b
      = do len <- fromBuf b {a = Int}
           readElems [] (integerToNat (cast len))
    where
      readElems : List a -> Nat -> Core (List a)
      readElems xs Z = pure (reverse xs)
      readElems xs (S k)
          = do val <- fromBuf b
               readElems (val :: xs) k

export
TTC a => TTC (List1 a) where
  toBuf b xxs
     = do toBuf b (head xxs)
          toBuf b (tail xxs)

  fromBuf b = do
    x <- fromBuf b
    xs <- fromBuf b
    pure (x ::: xs)

export
{n : Nat} -> TTC a => TTC (Vect n a) where
  toBuf b xs = writeAll xs
    where
      writeAll : forall n . Vect n a -> Core ()
      writeAll [] = pure ()
      writeAll (x :: xs) = do toBuf b x; writeAll xs

  fromBuf {n} b = rewrite sym (plusZeroRightNeutral n) in readElems [] n
    where
      readElems : Vect done a -> (todo : Nat) -> Core (Vect (todo + done) a)
      readElems {done} xs Z
          = pure (reverse xs)
      readElems {done} xs (S k)
          = do val <- fromBuf b
               rewrite (plusSuccRightSucc k done)
               readElems (val :: xs) k

export
(TTC a, Measure a) => TTC (PosMap a) where
  toBuf b = toBuf b . toList
  fromBuf b = fromList <$> fromBuf b

%hide Fin.fromInteger

count : List.Elem.Elem x xs -> Int
count Here = 0
count (There p) = 1 + count p

toLimbs : Integer -> List Int
toLimbs x
    = if x == 0
         then []
         else if x == -1 then [-1]
              else fromInteger (prim__and_Integer x 0xffffffff) ::
                   toLimbs (prim__shr_Integer x 32)

fromLimbs : List Int -> Integer
fromLimbs [] = 0
fromLimbs (x :: xs) = cast x + prim__shl_Integer (fromLimbs xs) 32

export
TTC Integer where
  toBuf b val
    = assert_total $ if val < 0
         then do tag 0
                 toBuf b (toLimbs (-val))
         else do tag 1
                 toBuf b (toLimbs val)
  fromBuf b
    = do val <- getTag
         case val of
              0 => do val <- fromBuf b
                      pure (-(fromLimbs val))
              1 => do val <- fromBuf b
                      pure (fromLimbs val)
              _ => corrupt "Integer"

export
TTC Bits8 where
  toBuf b x = toBuf b $ cast {to = Int} x
  fromBuf b = cast {from = Int} <$> fromBuf b

export
TTC Bits16 where
  toBuf b x = toBuf b $ cast {to = Int} x
  fromBuf b = cast {from = Int} <$> fromBuf b

export
TTC Bits32 where
  toBuf b x = toBuf b $ cast {to = Integer} x
  fromBuf b = cast {from = Integer} <$> fromBuf b

export
TTC Bits64 where
  toBuf b x = toBuf b $ cast {to = Integer} x
  fromBuf b = cast {from = Integer} <$> fromBuf b

export
TTC Int8 where
  toBuf b x = toBuf b $ cast {to = Int} x
  fromBuf b = cast {from = Int} <$> fromBuf b

export
TTC Int16 where
  toBuf b x = toBuf b $ cast {to = Int} x
  fromBuf b = cast {from = Int} <$> fromBuf b

export
TTC Int32 where
  toBuf b x = toBuf b $ cast {to = Int} x
  fromBuf b = cast {from = Int} <$> fromBuf b

export
TTC Int64 where
  toBuf b x = toBuf b $ cast {to = Integer} x
  fromBuf b = cast {from = Integer} <$> fromBuf b

export
TTC Nat where
  toBuf b val = toBuf b (cast {to=Integer} val)
  fromBuf b
     = do val <- fromBuf b
          pure (fromInteger val)

||| Get a file's modified time. If it doesn't exist, return 0 (UNIX Epoch)
export
modTime : String -> Core Timestamp
modTime fname
  = do Right f <- coreLift $ openFile fname Read
         | Left err => pure $ MkTimestamp 0 0 -- Beginning of Time :)
       Right t <- coreLift $ fileTime f
         | Left err => do coreLift $ closeFile f
                          pure $ MkTimestamp 0 0
       coreLift $ closeFile f
       pure $ t.mtime

export
hashFileWith : Maybe String -> String -> Core (Maybe String)
hashFileWith Nothing _ = pure Nothing
hashFileWith (Just sha256sum) fileName
  = do Right fileHandle <- coreLift $ popen
            (sha256sum ++ " \"" ++ osEscape fileName ++ "\"") Read
         | Left _ => err
       Right hashLine <- coreLift $ fGetLine fileHandle
         | Left _ =>
           do ignore $ coreLift $ pclose fileHandle
              err
       ignore $ coreLift $ pclose fileHandle
       let w@(_::_) = words hashLine
         | Nil => err
       pure $ Just $ last w
  where
    err : Core a
    err = coreFail $ InternalError ("Can't get " ++ sha256sum ++ " of " ++ fileName)
    osEscape : String -> String
    osEscape = if isWindows
      then id
      else escapeStringUnix

export
TTC a => TTC (SnocList a) where
  toBuf b xs
      = do toBuf b (TailRec_length xs)
           traverse_ (toBuf b) xs
    where
      ||| Tail-recursive length as buffer sizes can get large
      |||
      ||| Once we port to Idris2, can use Data.List.TailRec.length instead
      length_aux : SnocList a -> Int -> Int
      length_aux [<] len = len
      length_aux (_ :%: xs) len = length_aux xs (1 + len)

      TailRec_length : SnocList a -> Int
      TailRec_length xs = length_aux xs 0

  fromBuf b
      = do len <- fromBuf b {a = Int}
           readElems [<] (integerToNat (cast len))
    where
      readElems : SnocList a -> Nat -> Core (SnocList a)
      readElems xs Z = pure (reverse xs)
      readElems xs (S k)
          = do val <- fromBuf b
               readElems (val :%: xs) k

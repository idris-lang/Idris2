import System

import Data.Nat

data ArrayData : Type -> Type where [external]

-- We use `Integer` for indexing here instead of `Int` as in `Data.IOArray.Prims`
%extern prim__newArray : forall a . Integer -> a -> PrimIO (ArrayData a)
%extern prim__arrayGet : forall a . ArrayData a -> Integer -> PrimIO a
%extern prim__arraySet : forall a . ArrayData a -> Integer -> a -> PrimIO ()

record IOArray (n : Nat) a where
  constructor MkIOArray
  content : ArrayData a

newArray : HasIO io => (n : Nat) -> a -> io (IOArray n a)
newArray size v = pure (MkIOArray !(primIO (prim__newArray (cast size) v)))

writeArray :
     HasIO io
  => IOArray n a
  -> (m : Nat)
  -> {auto 0 lt : LT m n}
  -> a
  -> io ()
writeArray arr pos el = primIO (prim__arraySet (content arr) (cast pos) el)

readArray :
     HasIO io
  => IOArray n a
  -> (m : Nat)
  -> {auto 0 lt : LT m n}
  -> io a
readArray arr pos = primIO (prim__arrayGet (content arr) (cast pos))

toList : {n : _} -> HasIO io => IOArray n a -> io (List a)
toList arr = iter n reflexive []
where
  iter : (m : Nat) -> (0 lte : LTE m n) -> List a -> io (List a)
  iter 0     _ acc = pure acc
  iter (S k) p acc = readArray arr k >>= \el => iter k (lteSuccLeft p) (el :: acc)

main : IO ()
main = do
  x <- newArray 20 ""
  writeArray x 11 "World"
  writeArray x 10 "Hello"
  printLn !(toList x)

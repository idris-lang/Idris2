||| WIP: same as Data.List.Quantifiers but for lazy lists

module Data.List.Lazy.Quantifiers

import Data.DPair
import Data.List.Lazy

%default total

namespace Any

  -- Note: it is crucial here that we mark `xs` as `Lazy`, otherwise Idris
  --  will happily use `Delay` in the return index and give us a badly-behaved
  -- family!
  public export
  data Any : (p : a -> Type) -> (xs : LazyList a) -> Type where
    Here : {0 xs : Lazy (LazyList a)} -> p x -> Any p (x :: xs)
    There : {0 xs : Lazy (LazyList a)} -> Any p xs -> Any p (x :: xs)

  public export
  toExists : Any p xs -> Exists p
  toExists (Here prf) = Evidence _ prf
  toExists (There p) = toExists p

  public export
  toDPair : {xs : LazyList a} -> Any p xs -> DPair a p
  toDPair (Here prf) = (_ ** prf)
  toDPair (There p) = toDPair p

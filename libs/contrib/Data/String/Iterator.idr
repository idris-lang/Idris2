module Data.String.Iterator

import public Data.List.Lazy

%default total

-- Backend-dependent string iteration type.
export
data StringIterator : Type where [external]

-- This function is private
-- to avoid subverting the linearity guarantees of withString.
%foreign
  "scheme:blodwen-string-iterator-new"
private
fromString : String -> StringIterator

-- This function uses a linear string iterator
-- so that backends can use mutating iterators.
export
withString : String -> ((1 it : StringIterator) -> a) -> a
withString str f = f (fromString str)

-- We use a custom data type instead of Maybe (Char, StringIterator)
-- to remove one level of pointer indirection
-- in every iteration of something that's likely to be a hot loop,
-- and to avoid one allocation per character.
--
-- The Char field of Character is unrestricted for flexibility.
public export
data UnconsResult : Type where
  EOF : UnconsResult
  Character : (c : Char) -> (1 it : StringIterator) -> UnconsResult

-- We pass the whole string to the uncons function
-- to avoid yet another allocation per character
-- because for many backends, StringIterator can be simply an integer
-- (e.g. byte offset into an UTF-8 string).
%foreign
  "scheme:blodwen-string-iterator-next"
export
uncons : String -> (1 it : StringIterator) -> UnconsResult

export
foldl : (accTy -> Char -> accTy) -> accTy -> String -> accTy
foldl op acc str = withString str (loop acc)
  where
    loop : accTy -> (1 it : StringIterator) -> accTy
    loop acc it =
      case uncons str it of
        EOF => acc
        Character c it' => loop (acc `op` c) (assert_smaller it it')

export
unpack : String -> LazyList Char
unpack str = withString str unpack'
  where
    unpack' : (1 it : StringIterator) -> LazyList Char
    unpack' it =
      case uncons str it of
        EOF => []
        Character c it' => c :: Delay (unpack' $ assert_smaller it it')

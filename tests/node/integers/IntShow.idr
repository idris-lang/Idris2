module IntShow

-- This file to be deleted once these interfaces are added to prelude

firstCharIs : (Char -> Bool) -> String -> Bool
firstCharIs p "" = False
firstCharIs p str = p (assert_total (prim__strHead str))

primNumShow : (a -> String) -> Prec -> a -> String
primNumShow f d x = let str = f x in showParens (d >= PrefixMinus && firstCharIs (== '-') str) str

export
Show Int8 where
  showPrec = primNumShow prim__cast_Int8String

export
Show Int16 where
  showPrec = primNumShow prim__cast_Int16String

export
Show Int32 where
  showPrec = primNumShow prim__cast_Int32String

export
Show Int64 where
  showPrec = primNumShow prim__cast_Int64String

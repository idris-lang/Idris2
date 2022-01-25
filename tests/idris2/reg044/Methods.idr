data Foo = A | B | C

Eq Foo where
   A == A = True
   B == B = True
   C == C = True
   _ == _ = False

interface Read a where
  readPrefix : String -> Maybe (a, String)

  read : String -> Maybe a
  read str = case readPrefix str of
    Just (a, "") => pure a
    Nothing => Nothing

Read Foo where

  read "A" = A
  read "B" = B
  read "C" = C

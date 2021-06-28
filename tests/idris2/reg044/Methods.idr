data Foo = A | B | C

Eq Foo where
   A == A = True
   B == B = True
   C == C = True
   _ == _ = False

Ord Foo where
   A < B = True
   B < C = True
   _ < _ = False

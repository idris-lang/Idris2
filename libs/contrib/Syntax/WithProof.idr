module Syntax.WithProof

||| Until Idris2 supports the 'with (...) proof p' construct, here's a
||| poor-man's replacement.
prefix 10 @@
public export
(@@) : (t : a ) -> (u : a ** t = u)
(@@) x = ( x ** Refl)

module Syntax.WithProof

prefix 10 @@

||| Until Idris2 supports the 'with (...) proof p' construct, here's a
||| poor-man's replacement.
public export
(@@) : (t : a) -> (u : a ** t = u)
(@@) x = (x ** Refl)

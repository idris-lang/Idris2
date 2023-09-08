module B

import A

public export

--if you change the name of the function from BFromInteger to AInt here and in A.idr, as
--below, the problem disappears. Not sure the pattern here, but some names cause an issue
--and some do not
-- BFunc : AInt x => (a : x) -> Type
BFunc : BFromInteger x => (a : x) -> Type
BFunc a = (a = a)

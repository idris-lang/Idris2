data A = AA
data B = BB

interface TJSON a where
    constructor MkTJSON
    tJSON : a -> ()

interface TFFI a b | a where
    tFFI : a -> b

TJSON B where
  tJSON BB = ()

TFFI A B where
  tFFI AA = BB

(TFFI a b, TJSON b) => TJSON a where
  tJSON = tJSON . tFFI

test : ()
test = tJSON AA

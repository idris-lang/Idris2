module SimpleData

data Fwd a = FNil | (<|) a (Fwd a)
data Bwd a = BNil | (|>) (Bwd a) a

data Tree n l
  = Leaf l
  | Node (Tree n l) n (Tree n l)

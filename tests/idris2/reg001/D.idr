module D

-- %logging 10
func1 : Applicative f => (a -> f c) -> (b -> f d) -> (a, b) -> f (c, d)
func1 fn g (ma, mb) = MkPair <$> fn ma <*> ?gmb
-- %logging 0

-- %logging 10
mfunc : (a -> Maybe c) -> (b -> Maybe d) -> (a, b) -> Maybe (c, d)
mfunc fn g (ma, mb)
   = let pairapp = MkPair <$> fn ma in
         pairapp <*> g mb
%logging 0

func2 : (a -> c) -> (b -> d) -> a -> b -> (c, d)
func2 f g a b = MkPair (f a) (g b)

import Data.Ref

stsum : Num a => List a -> a
stsum xs
    = runST $
        do acc <- newRef 0
           add xs acc
           readRef acc
  where
    add : List a -> STRef s a -> ST s ()
    add [] ref = pure ()
    add (x :: xs) ref
        = do acc <- readRef ref
             writeRef ref (acc + x)
             add xs ref

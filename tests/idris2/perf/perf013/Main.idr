foo : Monad m => Int -> m ()
foo 0 = pure ()
foo n = do pure ()
           foo (n - 1)

bar : foo 1000000 === Just ()
bar = Refl

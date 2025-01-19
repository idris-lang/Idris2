module Case

listId : List a -> List a
listId xs = case xs of
  [] => []
  (x :: xs) => x :: listId xs

listRev : List a -> List a
listRev = \case
  [] => []
  (x :: xs) => listRev xs ++ [x]

listFilter2 : (p, q : a -> Bool) -> List a -> List a
listFilter2 p q xs
  = do x <- xs
       -- let pat
       let True = p x
         | False => []
       -- do pat
       True <- pure (q x)
         | False => []
       pure x

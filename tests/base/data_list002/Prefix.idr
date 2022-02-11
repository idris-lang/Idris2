import Data.List

test : prefixOfBy (\ n, str => str <$ guard (String.length str == n))
       [5,5]
       ["hello", "world", "this", "is", "not", "selected"]
       === Just (["hello", "world"], ["this", "is", "not", "selected"])
test = Refl

test2 : suffixOfBy (\ n, str => str <$ guard (String.length str == n))
       [4,2,8]
       ["hello", "world", "this", "is", "selected"]
       === Just (["hello", "world"], ["this", "is", "selected"])
test2 = Refl

test' : isPrefixOfBy (\ n, str => String.length str == n)
       [5,5]
       ["hello", "world", "this", "is", "not", "selected"]
       === True
test' = Refl

test2' : isSuffixOfBy (\ n, str => String.length str == n)
       [4,2,8]
       ["hello", "world", "this", "is", "selected"]
       === True
test2' = Refl

data NonEmpty : List a -> Type where
  IsNonEmpty : NonEmpty (x :: xs)

head : (xs : List a) -> NonEmpty xs => a
head (x :: xs) = x

failing "Can't find an implementation for NonEmpty xs."
    myHead : List a -> a
    myHead xs = head xs

failing """
Can't find
an implementation
  for NonEmpty xs.
"""
    myHead : List a -> a
    myHead xs = head xs


failing """
Can't
find


                  an implementation




for NonEmpty xs.
"""
    myHead : List a -> a
    myHead xs = head xs

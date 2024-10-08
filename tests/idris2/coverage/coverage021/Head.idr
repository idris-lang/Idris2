total
head : List a -> a
head (x :: xs) = x
head () impossible

total
head' : List a -> a
head' (x :: xs) = x
head' Z impossible

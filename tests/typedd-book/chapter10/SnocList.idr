import Data.List

data SnocList : List a -> Type where
     Empty : SnocList []
     Snoc : (x, xs : _) -> (rec : SnocList xs) -> SnocList (xs ++ [x])

snocListHelp : {input : _} ->
               (snoc : SnocList input) -> (rest : List a) -> SnocList (input ++ rest)
snocListHelp snoc [] = rewrite appendNilRightNeutral input in snoc
snocListHelp snoc (x :: xs)
    = rewrite appendAssociative input [x] xs in
              snocListHelp (Snoc x input snoc) xs

snocList : (xs : List a) -> SnocList xs
snocList xs = snocListHelp Empty xs

my_reverse_help : (input : List a) -> SnocList input -> List a
my_reverse_help [] Empty = []
my_reverse_help (xs ++ [x]) (Snoc x xs rec) = x :: my_reverse_help xs rec

my_reverse1 : List a -> List a
my_reverse1 input = my_reverse_help input (snocList input)

my_reverse : List a -> List a
my_reverse input with (snocList input)
  my_reverse [] | Empty = []
  my_reverse (xs ++ [x]) | (Snoc x xs rec) = x :: my_reverse xs | rec

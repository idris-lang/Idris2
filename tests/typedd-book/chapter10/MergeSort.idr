import Data.List

data SplitList : List a -> Type where
     SplitNil : SplitList []
     SplitOne : SplitList [x]
     SplitPair : (lefts : List a) -> (rights : List a) ->
                 SplitList (lefts ++ rights)

total
splitList : (xs : List a) ->  SplitList xs
splitList xs = splitListHelp xs xs
  where
    splitListHelp : (counter : List a) -> (xs : List a) -> SplitList xs
    splitListHelp _ [] = SplitNil
    splitListHelp _ [x] = SplitOne
    splitListHelp (_ :: _ :: ys) (x :: xs)
       = case splitListHelp ys xs of
              SplitNil => SplitOne
              SplitOne {x=y} => SplitPair [x] [y]
              SplitPair lefts rights => SplitPair (x :: lefts) rights
    splitListHelp _ xs = SplitPair [] xs

mergeSort : Ord a => List a -> List a
mergeSort input with (splitList input)
  mergeSort [] | SplitNil = []
  mergeSort [x] | SplitOne = [x]
  mergeSort (lefts ++ rights) | (SplitPair lefts rights)
         = merge (mergeSort lefts) (mergeSort rights)

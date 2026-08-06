module Text.Quantity

%default total

||| A quantity bounded by a minimum and, optionally, a maximum.
||| It can be used in certain lexers or parsers to specify
||| how many times an item is expected to appear.
public export
record Quantity where
  constructor Qty
  ||| Minimum number of occurrences.
  min : Nat
  ||| Optional maximum number of occurrences.
  max : Maybe Nat

public export
Show Quantity where
  show (Qty Z Nothing) = "*"
  show (Qty Z (Just (S Z))) = "?"
  show (Qty (S Z) Nothing) = "+"
  show (Qty min max) = "{" ++ show min ++ showMax ++ "}"
    where
      showMax : String
      showMax = case max of
                     Nothing => ","
                     Just max' => if min == max'
                                     then ""
                                     else "," ++ show max'

||| Create a `Quantity` with the given lower and upper bounds. {min,max}
public export
between : Nat -> Nat -> Quantity
between min max = Qty min (Just max)

||| Create a `Quantity` with only a lower bound. {min,}
public export
atLeast : Nat -> Quantity
atLeast min = Qty min Nothing

||| Create a `Quantity` from zero to the given upper bound. {0,max}
public export
atMost : Nat -> Quantity
atMost max = Qty 0 (Just max)

||| Create a `Quantity` requiring an exact number of occurrences. {n}
public export
exactly : Nat -> Quantity
exactly n = Qty n (Just n)

||| Check whether a `Quantity`'s bounds are well-formed, i.e. min <= max.
public export
inOrder : Quantity -> Bool
inOrder (Qty min Nothing) = True
inOrder (Qty min (Just max)) = min <= max

module Text.Quantity

%default total

public export
record Quantity where
  constructor Qty
  min : Nat
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

public export
between : Nat -> Nat -> Quantity
between min max = Qty min (Just max)

public export
atLeast : Nat -> Quantity
atLeast min = Qty min Nothing

public export
atMost : Nat -> Quantity
atMost max = Qty 0 (Just max)

public export
exactly : Nat -> Quantity
exactly n = Qty n (Just n)

public export
inOrder : Quantity -> Bool
inOrder (Qty min Nothing) = True
inOrder (Qty min (Just max)) = min <= max

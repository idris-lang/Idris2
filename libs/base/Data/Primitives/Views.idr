module Data.Primitives.Views

-- We need all the believe_mes and asserts throughout this file because we're
-- working with primitive here! We also have separate implementations per
-- primitive, rather than using interfaces, because we're only going to trust
-- the primitive implementations.

namespace IntegerV
  ||| View for expressing a number as a multiplication + a remainder
  public export
  data Divides : Integer -> (d : Integer) -> Type where
       DivByZero : Divides x 0
       DivBy : (div, rem : _) ->
               (prf : rem >= 0 && rem < d = True) ->
               Divides ((d * div) + rem) d

  ||| Covering function for the `Divides` view
  public export
  divides : (val : Integer) -> (d : Integer) -> Divides val d
  divides val 0 = DivByZero
  divides val d
         = assert_total $
             let dividend = if d < 0 then -(val `div` abs d)
                                     else val `div` d
                 remainder = abs (val - dividend * d) in
                 believe_me (DivBy {d} dividend remainder
                            (believe_me (Refl {x = True})))

  ||| View for recursion over Integers
  public export
  data IntegerRec : Integer -> Type where
       IntegerZ : IntegerRec 0
       -- adding the constant (-1 or 1) on the left keeps the view
       -- similar to the inductive definition of natural numbers, and
       -- is usually compatible with pattern matching on arguments
       -- left-to-right.
       IntegerSucc : IntegerRec (-1 + n) -> IntegerRec n
       IntegerPred : IntegerRec (1 + (-n)) -> IntegerRec (-n)

  ||| Covering function for `IntegerRec`
  public export
  integerRec : (x : Integer) -> IntegerRec x
  integerRec 0 = IntegerZ
  integerRec x = if x > 0 then IntegerSucc (assert_total (integerRec (-1 + x)))
                      else believe_me (IntegerPred {n = -x}
                                (assert_total (believe_me (integerRec (1 + x)))))

namespace IntV
  ||| View for expressing a number as a multiplication + a remainder
  public export
  data Divides : Int -> (d : Int) -> Type where
       DivByZero : IntV.Divides x 0
       DivBy : (div, rem : _) ->
               (prf : rem >= 0 && rem < d = True) ->
               IntV.Divides ((d * div) + rem) d

  -- I have assumed, but not actually verified, that this will still
  -- give a right result (i.e. still adding up) when the Ints overflow.
  -- TODO: Someone please check this and fix if necessary...

  ||| Covering function for the `Divides` view
  public export
  divides : (val : Int) -> (d : Int) -> Divides val d
  divides val 0 = DivByZero
  divides val d
         = assert_total $
             let dividend = if d < 0 then -(val `div` abs d)
                                     else val `div` d
                 remainder = abs (val - dividend * d) in
                 believe_me (DivBy {d} dividend remainder
                            (believe_me (Refl {x = True})))

  ||| View for recursion over Ints
  public export
  data IntRec : Int -> Type where
       IntZ : IntRec 0
       -- adding the constant (-1 or 1) on the left keeps the view
       -- similar to the inductive definition of natural numbers, and
       -- is usually compatible with pattern matching on arguments
       -- left-to-right.
       IntSucc : IntRec (-1 + n) -> IntRec n
       IntPred : IntRec (1 + (-n)) -> IntRec (-n)

  ||| Covering function for `IntRec`
  public export
  intRec : (x : Int) -> IntRec x
  intRec 0 = IntZ
  intRec x = if x > 0 then IntSucc (assert_total (intRec (-1 + x)))
                      else believe_me (IntPred {n = -x}
                                (assert_total (believe_me (intRec (1 + x)))))

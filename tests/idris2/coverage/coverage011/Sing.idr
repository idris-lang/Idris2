module Sing

%default total

data Fing : Type -> Type where
  StringFing : String -> Fing String
  BoolFing : Bool -> Fing Bool

stringFing : Fing String -> String
stringFing (StringFing s) = s

boolFing : Fing Bool -> Bool
boolFing (BoolFing b) = b

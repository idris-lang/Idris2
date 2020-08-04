import Data.Maybe

%default total

FromString Int where
  fromString x = cast x

test1 : Int
test1 = "42"

test2 : Int
test2 = "abc"

convert : String -> Maybe Bool
convert "True" = Just True
convert "False" = Just False
convert _ = Nothing

fromString : (str : String) -> {auto prf : IsJust (convert str)} -> Bool
fromString str {prf} with (convert str)
  fromString str {prf = ItIsJust} | (Just ret) = ret

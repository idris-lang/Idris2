||| This tests that issue #3280 has been fixed. With the former
||| implementation of `unpack`, the compiler would not produce
||| an error in a reasonable amount of time.
import Data.String

%default total

data Format = FInt Format        -- %d
            | FString Format     -- %s
            | FOther Char Format
            | FEnd

format : List Char -> Format
format Nil = FEnd
format ('%' :: 'd' :: xs) = FInt (format xs)
format ('%' :: 's' :: xs) = FString (format xs)
format (x :: xs) = FOther x (format xs)


0 InterpFormat : Format -> Type
InterpFormat (FInt f)     = Int    -> InterpFormat f
InterpFormat (FString f)  = String -> InterpFormat f
InterpFormat (FOther _ f) = InterpFormat f
InterpFormat FEnd         = String

formatString : String -> Format
formatString s = format (unpack s)

toFunction : (fmt : Format) -> String -> InterpFormat fmt
toFunction (FInt x) str     = \y => toFunction x (str ++ show y)
toFunction (FString x) str  = \y => toFunction x (str ++ y)
toFunction (FOther c x) str = toFunction x (str ++ singleton c)
toFunction FEnd str         = str

printf : (s : String) -> InterpFormat (formatString s)
printf s = toFunction (formatString s) ""

message : String
message = printf "My name is %s and I am %d years old"

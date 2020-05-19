import Data.Strings
import Data.Vect

StringOrInt : Bool -> Type
StringOrInt False = String
StringOrInt True = Int

getStringOrInt : (isInt : Bool) -> StringOrInt isInt
getStringOrInt False = "Ninety four"
getStringOrInt True = 94

valToString : (isInt : Bool) -> StringOrInt isInt -> String
valToString False y = trim y
valToString True y = cast y

valToString' : (isInt : Bool) -> (case isInt of
                                       False => String
                                       True => Int) -> String
valToString' False y = trim y
valToString' True y = cast y

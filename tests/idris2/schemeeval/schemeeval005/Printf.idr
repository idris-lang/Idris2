module Printf

import Prelude
import Data.String

data Arg
    = AInt      Arg
    | AOther    Char Arg
    | AEnd

buildArg : List Char -> Arg
buildArg fmt = case fmt of
    '%' :: 'i' :: fmtTail   => AInt (buildArg fmtTail)
    c :: fmtTail            => AOther c (buildArg fmtTail)
    Nil                     => AEnd

argToType : Arg -> Type -> Type
argToType a result = case a of
    AInt fmtTail      => Int -> argToType fmtTail result
    AOther _ fmtTail  => argToType fmtTail result
    AEnd              => result

-- PrintfType "foo" result = result
-- PrintfType "%i\n" result = Int -> result
-- etc
PrintfType : String -> Type -> Type
PrintfType fmt result = argToType (buildArg (unpack fmt)) result

sprintf : (fmt : String) -> PrintfType fmt String
sprintf fmt = go "" (buildArg (unpack fmt)) where
    go : String -> (arg : Arg) -> argToType arg String
    go strTail arg = case arg of
        AInt fmtTail        => \i : Int => go (strTail ++ show i) fmtTail
        AOther c fmtTail    => go (strTail ++ singleton c) fmtTail
        AEnd                => strTail

test : ?result
test = sprintf "%i%i%i%i%i%i"

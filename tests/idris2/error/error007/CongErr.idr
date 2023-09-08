import Data.Fin

fsprf : x === y -> Fin.FS x = FS y
fsprf p = cong _ p

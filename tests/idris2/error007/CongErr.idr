import Data.Fin

fsprf : x === y -> FS x = FS y
fsprf p = cong _ p

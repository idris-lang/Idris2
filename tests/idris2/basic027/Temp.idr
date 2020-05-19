module Temp

import Data.List

safeHead : (l : List a) -> {auto pr : NonEmpty l} -> a
safeHead [] = absurd pr
safeHead (x::xs) = x

safeHead1 : (l : List a) -> {auto pr : NonEmpty l} -> a
safeHead1 @{pr} [] = absurd pr
safeHead1 (x::xs) = x

safeHead2 : (l : List a) -> {auto pr : NonEmpty l} -> a
safeHead2 @{t} [] = absurd t
safeHead2 (x::xs) = x

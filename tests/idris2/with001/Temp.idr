module Temp

import Data.List

safeStrHead : (s : String) -> {pr : NonEmpty (unpack s)} -> Char
safeStrHead s with (unpack s)
  safeStrHead s | [] = absurd pr
  safeStrHead s | (c::_) = c

safeStrHead1 : (s : String) -> {pr : NonEmpty (unpack s)} -> Char
safeStrHead1 s with (unpack s)
  safeStrHead1 {pr} s | [] = absurd pr
  safeStrHead1 s | (c::_) = c

safeStrHead2 : (s : String) -> {pr : NonEmpty (unpack s)} -> Char
safeStrHead2 s with (unpack s)
  safeStrHead2 {pr=foo} s | [] = absurd foo
  safeStrHead2 s | (c::_) = c

safeStrHead3 : (s : String) -> {pr : NonEmpty (unpack s)} -> Char
safeStrHead3 {pr=foo} s with (unpack s)
  safeStrHead3 s | [] = absurd foo
  safeStrHead3 s | (c::_) = c

safeStrHead4 : (s : String) -> {pr : NonEmpty (unpack s)} -> Char
safeStrHead4 {pr=foo} s with (unpack s)
  safeStrHead4 {pr=bar} s | [] = absurd bar
  safeStrHead4 s | (c::_) = c


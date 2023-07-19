module Resugar

import Prefix
import Infix

cannotDo : !! a (!! a) === a
cannotDo = Refl

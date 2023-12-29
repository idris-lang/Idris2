module DefaultImplicitsInImpls

import Data.Vect

%default total

[TunableImpl] {default False fancy : Bool} -> Show Nat where
  show x = if fancy then "!!! hohoho !!!" else "no fancy"

X0 : String
X0 = show @{TunableImpl} 5

x0Corr : X0 === "no fancy"
x0Corr = Refl

X1 : String
X1 = show @{TunableImpl {fancy=True}} 5

x1Corr : X1 === "!!! hohoho !!!"
x1Corr = Refl

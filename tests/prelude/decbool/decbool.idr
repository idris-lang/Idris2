import Decidable.Equality
import Decidable.Equality.Bool

notBTMeansBF : (b : Bool) -> (not b = True) -> (b = False)
notBTMeansBF True p = absurd p
notBTMeansBF False p = Refl

result : (b : Bool) -> (x ** b = not x)
result b with (decEq b True)
  result b | Yes prf =
    MkDPair False prf
  result b | No contra =
    let
      prf = invertContraBool b True contra
    in
    rewrite notBTMeansBF b prf in
    MkDPair True Refl

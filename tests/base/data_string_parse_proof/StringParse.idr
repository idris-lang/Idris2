import Data.String
import Data.Nat

%default total

posNat : Maybe Nat
posNat = parsePositive "2"

posNatProof : Main.posNat === Just 2
posNatProof = Refl

int : Maybe Integer
int = parseInteger "-123"

integerProof : Main.int === Just (-123)
integerProof = Refl


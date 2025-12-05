import Data.Vect

export typebind infixr 0 ***
export infix 1 ***

namespace DPairType

  public export
  (***) : (a : Type) -> (a -> Type) -> Type
  (***) = DPair

namespace DPairVal

  public export
  (***) : {0 f : _} -> (x : a) -> f x -> (x : a) *** f x
  (***) = MkDPair

anotherPair : (a : Type) *** (n : Nat) *** Vect n a
anotherPair = Nat *** (5 *** [1, 2, 3, 4, 5])

import Data.Vect

MkBig : Nat -> Type
MkBig Z = Int
MkBig (S k) = ((n ** Vect n Int), MkBig k)

bigEx : (n : Nat) -> MkBig n
bigEx Z = 94
bigEx (S k) = ((2 ** [0,0]), bigEx k)

data VWrap : Type -> Type where
     MkVWrap : (0 n : Nat) -> Vect n a -> VWrap a

MkBig' : Nat -> Type
MkBig' Z = Int
MkBig' (S k) = (VWrap Int, MkBig' k)

namespace Foo
  public
  export
  bigEx' : (n : Nat) -> MkBig' n
  bigEx' Z = 94
  bigEx' (S k) = (MkVWrap 1 [0], bigEx' k)

eqBigs : bigEx 1000000 = bigEx 1000000
eqBigs = Refl

eqBigs' : bigEx' 800000 = bigEx' 800000
eqBigs' = Refl


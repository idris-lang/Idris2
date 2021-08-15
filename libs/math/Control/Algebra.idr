module Control.Algebra

infixl 6 <->
infixl 7 <.>

public export
interface Semigroup ty => SemigroupV ty where
  semigroupOpIsAssociative : (l, c, r : ty) ->
    l <+> (c <+> r) = (l <+> c) <+> r

public export
interface (Monoid ty, SemigroupV ty) => MonoidV ty where
  monoidNeutralIsNeutralL : (l : ty) -> l <+> neutral {ty} = l
  monoidNeutralIsNeutralR : (r : ty) -> neutral {ty} <+> r = r

||| Sets equipped with a single binary operation that is associative,
||| along with a neutral element for that binary operation and
||| inverses for all elements. Satisfies the following laws:
|||
||| + Associativity of `<+>`:
|||     forall a b c, a <+> (b <+> c) == (a <+> b) <+> c
||| + Neutral for `<+>`:
|||     forall a,     a <+> neutral   == a
|||     forall a,     neutral <+> a   == a
||| + Inverse for `<+>`:
|||     forall a,     a <+> inverse a == neutral
|||     forall a,     inverse a <+> a == neutral
public export
interface MonoidV ty => Group ty where
  inverse : ty -> ty

  groupInverseIsInverseR : (r : ty) -> inverse r <+> r = neutral {ty}

(<->) : Group ty => ty -> ty -> ty
(<->) left right = left <+> (inverse right)

||| Sets equipped with a single binary operation that is associative
||| and commutative, along with a neutral element for that binary
||| operation and inverses for all elements. Satisfies the following
||| laws:
|||
||| + Associativity of `<+>`:
|||     forall a b c, a <+> (b <+> c) == (a <+> b) <+> c
||| + Commutativity of `<+>`:
|||     forall a b,   a <+> b         == b <+> a
||| + Neutral for `<+>`:
|||     forall a,     a <+> neutral   == a
|||     forall a,     neutral <+> a   == a
||| + Inverse for `<+>`:
|||     forall a,     a <+> inverse a == neutral
|||     forall a,     inverse a <+> a == neutral
public export
interface Group ty => AbelianGroup ty where
  groupOpIsCommutative : (l, r : ty) -> l <+> r = r <+> l

||| A homomorphism is a mapping that preserves group structure.
public export
interface (Group a, Group b) => GroupHomomorphism a b where
  to : a -> b

  toGroup : (x, y : a) ->
    to (x <+> y) = (to x) <+> (to y)

||| Sets equipped with two binary operations, one associative and
||| commutative supplied with a neutral element, and the other
||| associative, with distributivity laws relating the two operations.
||| Satisfies the following laws:
|||
||| + Associativity of `<+>`:
|||     forall a b c, a <+> (b <+> c) == (a <+> b) <+> c
||| + Commutativity of `<+>`:
|||     forall a b,   a <+> b         == b <+> a
||| + Neutral for `<+>`:
|||     forall a,     a <+> neutral   == a
|||     forall a,     neutral <+> a   == a
||| + Inverse for `<+>`:
|||     forall a,     a <+> inverse a == neutral
|||     forall a,     inverse a <+> a == neutral
||| + Associativity of `<.>`:
|||     forall a b c, a <.> (b <.> c) == (a <.> b) <.> c
||| + Distributivity of `<.>` and `<+>`:
|||     forall a b c, a <.> (b <+> c) == (a <.> b) <+> (a <.> c)
|||     forall a b c, (a <+> b) <.> c == (a <.> c) <+> (b <.> c)
public export
interface Group ty => Ring ty where
  (<.>) : ty -> ty -> ty

  ringOpIsAssociative   : (l, c, r : ty) ->
    l <.> (c <.> r) = (l <.> c) <.> r
  ringOpIsDistributiveL : (l, c, r : ty) ->
    l <.> (c <+> r) = (l <.> c) <+> (l <.> r)
  ringOpIsDistributiveR : (l, c, r : ty) ->
    (l <+> c) <.> r = (l <.> r) <+> (c <.> r)

||| Sets equipped with two binary operations, one associative and
||| commutative supplied with a neutral element, and the other
||| associative supplied with a neutral element, with distributivity
||| laws relating the two operations. Satisfies the following laws:
|||
||| +  Associativity of `<+>`:
|||     forall a b c, a <+> (b <+> c) == (a <+> b) <+> c
||| + Commutativity of `<+>`:
|||     forall a b,   a <+> b         == b <+> a
||| + Neutral for `<+>`:
|||     forall a,     a <+> neutral   == a
|||     forall a,     neutral <+> a   == a
||| + Inverse for `<+>`:
|||     forall a,     a <+> inverse a == neutral
|||     forall a,     inverse a <+> a == neutral
||| + Associativity of `<.>`:
|||     forall a b c, a <.> (b <.> c) == (a <.> b) <.> c
||| + Neutral for `<.>`:
|||     forall a,     a <.> unity     == a
|||     forall a,     unity <.> a     == a
||| + Distributivity of `<.>` and `<+>`:
|||     forall a b c, a <.> (b <+> c) == (a <.> b) <+> (a <.> c)
|||     forall a b c, (a <+> b) <.> c == (a <.> c) <+> (b <.> c)
public export
interface Ring ty => RingWithUnity ty where
  unity : ty

  unityIsRingIdL : (l : ty) -> l <.> unity = l
  unityIsRingIdR : (r : ty) -> unity <.> r = r

||| Sets equipped with two binary operations – both associative,
||| commutative and possessing a neutral element – and distributivity
||| laws relating the two operations. All elements except the additive
||| identity should have a multiplicative inverse. Should (but may
||| not) satisfy the following laws:
|||
||| + Associativity of `<+>`:
|||     forall a b c, a <+> (b <+> c) == (a <+> b) <+> c
||| + Commutativity of `<+>`:
|||     forall a b,   a <+> b         == b <+> a
||| + Neutral for `<+>`:
|||     forall a,     a <+> neutral   == a
|||     forall a,     neutral <+> a   == a
||| + Inverse for `<+>`:
|||     forall a,     a <+> inverse a == neutral
|||     forall a,     inverse a <+> a == neutral
||| + Associativity of `<.>`:
|||     forall a b c, a <.> (b <.> c) == (a <.> b) <.> c
||| + Unity for `<.>`:
|||     forall a,     a <.> unity     == a
|||     forall a,     unity <.> a     == a
||| + InverseM of `<.>`, except for neutral
|||     forall a /= neutral,  a <.> inverseM a == unity
|||     forall a /= neutral,  inverseM a <.> a == unity
||| + Distributivity of `<.>` and `<+>`:
|||     forall a b c, a <.> (b <+> c) == (a <.> b) <+> (a <.> c)
|||     forall a b c, (a <+> b) <.> c == (a <.> c) <+> (b <.> c)
public export
interface RingWithUnity ty => Field ty where
  inverseM : (x : ty) -> Not (x = neutral {ty}) -> ty

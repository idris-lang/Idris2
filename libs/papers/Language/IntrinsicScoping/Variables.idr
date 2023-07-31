module Language.IntrinsicScoping.Variables

import Decidable.Equality
import Data.Nat
import Data.Nat.Order
import Data.SnocList

%default total

------------------------------------------------------------------------------
-- De Bruijn indices
------------------------------------------------------------------------------

||| We do not really care about the notion of names used here
||| as long as it has a decidable notion of equality.
||| String will do for now
export
Name : Type
Name = String

export
FromString Name where
  fromString = id

STRING : DecEq String
STRING = %search

export
DecEq Name where
  decEq = decEq @{STRING}

||| A context of De Bruijn indices is right-to-left.
||| Just like in typing rules, newly bound variables are added
||| at the most local end with index 0, and all other variables
||| see their index shifted by 1.
public export
IContext : Type
IContext = SnocList Name

||| De Bruijn indices are right-to-left, starting from 0
public export
data AtIndex : Nat -> Name -> IContext -> Type where
  Z : AtIndex 0 nm (g :< nm)
  S : AtIndex n nm g -> AtIndex (S n) nm (g :< _)

||| An index is the pairing of its encoding as a natural number
||| and the proof it is valid
public export
record Index (nm : Name) (ctx : IContext) where
  constructor MkIndex
  getIndex : Nat
  0 validIndex : AtIndex getIndex nm ctx

namespace Index

  public export
  fresh : Index nm (ctx :< nm)
  fresh = MkIndex 0 Z

  public export
  weaken : Index nm ctx -> Index nm (ctx :< _)
  weaken (MkIndex n p) = MkIndex (S n) (S p)

  export
  Injective Index.weaken where
    injective {x = MkIndex m p} {y = MkIndex m p} Refl = Refl

  public export
  data View : Index nm ctx -> Type where
    Z : View (Index.fresh {nm, ctx})
    S : (p : Index nm ctx) -> View (weaken p)

  public export
  view : (p : Index nm ctx) -> View p
  view (MkIndex 0 Z) = Z
  view (MkIndex (S i) (S prf)) = S (MkIndex i prf)

  export
  isLast : {g : _} -> Index nm ([<x] <+> g) -> Either (nm === x) (Index nm g)
  isLast {g = [<]} v@_ with (view v)
    _ | Z = Left Refl
    _ | S v' = Right v'
  isLast {g = (sx :< y)} v@_ with (view v)
    _ | Z = Right fresh
    _ | S v' = map weaken (isLast v')

  public export
  delete : {g : IContext} -> Index nm g -> IContext
  delete v@_ with (view v)
    delete {g = g :< _} v@_ | Z = g
    delete {g = _ :< x} v@_ | S n = delete n :< x

  export
  thicken : (v : Index nm g) -> (v' : Index nm' g) ->
            Either (nm === nm', v ~=~ v') (Index nm' (delete v))
  thicken v@_ w@_ with (view v) | (view w)
    _ | Z | Z = Left (Refl, Refl)
    _ | Z | S w' = Right w'
    _ | S _ | Z = Right fresh
    _ | S v' | S w' with (thicken v' w')
      _ | Left (Refl, p) = Left (Refl, cong weaken p)
      _ | Right res = Right (weaken res)

  export
  irrelevantAtIndex :
    (p : AtIndex n nm g) ->
    (q : AtIndex n nm' g) ->
    (nm === nm', p ~=~ q)
  irrelevantAtIndex Z Z = (Refl, Refl)
  irrelevantAtIndex (S p) (S q) with (irrelevantAtIndex p q)
    irrelevantAtIndex (S p) (S q) | (Refl, eq) = (Refl, cong S eq)

  export
  hetEqDec : (v : Index nm g) -> (w : Index nm' g) ->
             Dec (nm === nm', v ~=~ w)
  hetEqDec (MkIndex m p) (MkIndex n q) with (decEq m n)
    _ | No neq = No (\ (Refl, Refl) => neq Refl)
    hetEqDec (MkIndex m p) (MkIndex m q) | Yes Refl
      with 0 (snd (irrelevantAtIndex p q))
      hetEqDec (MkIndex m p) (MkIndex m p) | Yes Refl | Refl = Yes (Refl, Refl)

------------------------------------------------------------------------------
-- De Bruijn levels
------------------------------------------------------------------------------

||| A context of De Bruijn levels is left-to-right
||| Newly bound variables are added at the far end, with index (length ctx).
||| This has the advantage that all other variables have an unchanged level.
public export
LContext : Type
LContext = List Name

public export
data AtLevel : Nat -> Name -> LContext -> Type where
  H : {0 ctx : LContext} -> {0 nm : String} ->
      n = length ctx -> AtLevel n nm (nm :: ctx)
  T : {0 ctx : LContext} -> {0 nm : String} ->
      AtLevel n nm ctx -> AtLevel n nm (_ :: ctx)

levelIsFin : LTE (length ctx) i -> Not (AtLevel i nm ctx)
levelIsFin lte (H Refl) = void (succNotLTEpred lte)
levelIsFin lte (T p) = levelIsFin (lteSuccLeft lte) p

||| A level is the pairing of its encoding as a natural number
||| and the proof it is valid
public export
record Level (nm : Name) (ctx : LContext) where
  constructor MkLevel
  getLevel : Nat
  0 validIndex : AtLevel getLevel nm ctx

namespace Level

  export
  weaken : Level nm ctx -> Level nm (_ :: ctx)
  weaken (MkLevel n prf) = MkLevel n (T prf)

  export
  fresh : {ctx : _} -> Level nm (nm :: ctx)
  fresh = MkLevel (length ctx) (H Refl)

  public export
  data View : Level nm ctx -> Type where
    Z : View (Level.fresh {nm, ctx})
    S : (p : Level nm ctx) -> View (weaken p)

  invertH : (prf : AtLevel (length ctx) nm (nm' :: ctx)) ->
            (nm === nm', prf ~=~ H {nm, ctx} Refl)
  invertH (H Refl) = (Refl, Refl)
  invertH (T p) = void (levelIsFin reflexive p)

  invertT : (prf : AtLevel l nm (nm' :: ctx)) ->
            Not (l === length ctx) ->
            (p' : AtLevel l nm ctx ** prf === T p')
  invertT (H eq) neq = void (neq eq)
  invertT (T p) neq = (p ** Refl)

  viewAux :
    {l : Nat} -> (0 p : AtLevel l nm (nm' :: ctx)) ->
    (0 p' : AtLevel l nm ctx) -> (0 _ : p === T p') ->
    View (MkLevel l p)
  viewAux .(T p') p' Refl = S (MkLevel l p')

  public export
  view : {ctx : _} -> (p : Level nm ctx) -> View p
  view  {ctx = nm :: ctx} (MkLevel l p) with (decEq l (length ctx))
    view {ctx = nm :: ctx} (MkLevel .(length ctx) p)
      | Yes Refl with 0 (snd (invertH p))
      view {ctx = nm :: ctx} (MkLevel .(length ctx) .(H Refl))
        | Yes Refl | Refl = Z
    view (MkLevel l p) | No neq = viewAux p _ (snd (invertT p neq))
  view (MkLevel _ (H prf)) impossible
  view (MkLevel _ (T x)) impossible

  export
  irrelevantAtLevel :
    (p : AtLevel n nm ctx) ->
    (q : AtLevel n nm' ctx) ->
    (nm === nm', p ~=~ q)
  irrelevantAtLevel (H Refl) (H Refl) = (Refl, Refl)
  irrelevantAtLevel (H Refl) (T q) = void (levelIsFin reflexive q)
  irrelevantAtLevel (T p) (H Refl) = void (levelIsFin reflexive p)
  irrelevantAtLevel (T p) (T q) with (irrelevantAtLevel p q)
    irrelevantAtLevel (T p) (T p) | (Refl, Refl) = (Refl, Refl)

  export
  hetEqDec : (v : Level nm g) -> (w : Level nm' g) ->
             Dec (nm === nm', v ~=~ w)
  hetEqDec (MkLevel m p) (MkLevel n q) with (decEq m n)
    _ | No neq = No (\ (Refl, Refl) => neq Refl)
    hetEqDec (MkLevel m p) (MkLevel m q) | Yes Refl
      with 0 (snd (irrelevantAtLevel p q))
      hetEqDec (MkLevel m p) (MkLevel m p) | Yes Refl | Refl = Yes (Refl, Refl)

------------------------------------------------------------------------------
-- Conversion
------------------------------------------------------------------------------

public export
rev : List a -> SnocList a
rev [] = [<]
rev (x :: xs) = rev xs :< x

data Plus : (m, n, p : Nat) -> Type where
  PlusZ : Plus 0 n n
  PlusS : Plus m n p -> Plus (S m) n (S p)

zeroPlusRight : (m : Nat) -> Plus m 0 m
zeroPlusRight 0 = PlusZ
zeroPlusRight (S m) = PlusS (zeroPlusRight m)

succPlusRight : Plus m n p -> Plus m (S n) (S p)
succPlusRight PlusZ = PlusZ
succPlusRight (PlusS p) = PlusS (succPlusRight p)

0 plusIsGreater : Plus m n p -> LTE n p
plusIsGreater PlusZ = reflexive
plusIsGreater (PlusS prf) = lteSuccRight (plusIsGreater prf)

levelLT : {ctx : _} -> AtLevel i nm ctx -> LT i (length ctx)
levelLT (H Refl) = reflexive
levelLT (T p) = LTESucc (lteSuccLeft (levelLT p))

export
lteIsPlus : {n : Nat} -> LTE m n -> Plus (minus n m) m n
lteIsPlus LTEZero = rewrite minusZeroRight n in zeroPlusRight n
lteIsPlus (LTESucc p) = succPlusRight (lteIsPlus p)

namespace Invariant

  export
  asIndex : {ls : _} ->
            AtLevel n nm ls ->
            AtIndex (length ls `minus` S n) nm (rev ls)
  asIndex p = go p (lteIsPlus (levelLT p)) where

    go : forall n, nm, ls, i.
         AtLevel n nm ls ->
         Plus i (S n) (length ls) ->
         AtIndex i nm (rev ls)
    go (H Refl) PlusZ = Z
    go (H Refl) (PlusS prf) = void (succNotLTEpred (plusIsGreater prf))
    go (T p) PlusZ = void (levelIsFin reflexive p)
    go (T p) (PlusS prf) = S (go p prf)



export
asIndex : {ls : _} -> Level nm ls -> Index nm (rev ls)
asIndex (MkLevel n prf) = MkIndex (length ls `minus` S n) (asIndex prf)

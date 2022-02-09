||| This module is based on Todd Waugh Ambridge's blog post series
||| "Search over uniformly continuous decidable predicates on
||| infinite collections of types"
||| https://www.cs.bham.ac.uk/~txw467/tychonoff/InfiniteSearch1.html

module Search.Tychonoff

import Data.DPair

%default total

Extensionality : Type
Extensionality
  = {a : Type} -> {b : a -> Type} ->
    {f, g : (x : a) -> b x} ->
    ((x : a) -> f x === g x) -> f === g

Pred : Type -> Type
Pred a = a -> Type

0 Decidable : Pred a -> Type
Decidable p = (x : a) -> Dec (p x)

||| A type is searchable if for any
||| p a decidable predicate over that type
||| x can be found such that if there exists a
||| x0 satisfying p then x also satisfies p
0 IsSearchable : Type -> Type
IsSearchable a
  = (0 p : Pred a) -> Decidable p ->
    (x : a ** (x0 : a) -> p x0 -> p x)

infix 0 <->
record (<->) (a, b : Type) where
  constructor MkIso
  forwards  : a -> b
  backwards : b -> a
  inverseL  : (x : a) -> backwards (forwards x) === x
  inverseR  : (y : b) -> forwards (backwards y) === y

||| Searchable is closed under isomorphisms
map : (a <-> b) -> IsSearchable a -> IsSearchable b
map (MkIso f g _ inv) search p pdec =
  let (xa ** prfa) = search (p . f) (\ x => pdec (f x)) in
  (f xa ** \ xb, pxb => prfa (g xb) $ replace {p} (sym $ inv xb) pxb)

interface Searchable (0 a : Type) where
  search : IsSearchable a

Inhabited : Type -> Type
Inhabited a = a

SearchableIsInhabited : IsSearchable a -> Inhabited a
SearchableIsInhabited search = fst (search (\ _ => ()) (\ _ => Yes ()))

-- Finite types are trivially searchable

||| Unit is searchable
Searchable () where
  search p pdef = (() ** \ (), prf => prf)

||| Bool is searchable
Searchable Bool where
  search p pdec = case pdec True of
    -- if p True holds we're done
    Yes prf   => MkDPair True $ \ _, _ => prf
    -- otherwise p False is our best bet
    No contra => MkDPair False $ \case
      False => id
      True  => absurd . contra

||| Searchable is closed under finite sum
-- Note that this would enable us to go back and prove Bool searchable
-- via the iso Bool <-> Either () ()
(Searchable a, Searchable b) => Searchable (Either a b) where
  search p pdec =
    let (xa ** prfa) = search (p . Left) (\ xa => pdec (Left xa)) in
    let (xb ** prfb) = search (p . Right) (\ xb => pdec (Right xb)) in
    case pdec (Left xa) of
      Yes pxa => (Left xa ** \ _, _ => pxa)
      No npxa => case pdec (Right xb) of
        Yes pxb => (Right xb ** \ _, _ => pxb)
        No npxb => MkDPair (Left xa) $ \case
          Left xa' => \ pxa' => absurd (npxa (prfa xa' pxa'))
          Right xb' => \ pxb' => absurd (npxb (prfb xb' pxb'))

||| Searchable is closed under finite product
(Searchable a, Searchable b) => Searchable (a, b) where
  search p pdec =
    -- How cool is that use of choice?
    let (fb ** prfb) = Pair.choice $ \ a => search (p . (a,)) (\ b => pdec (a, b)) in
    let (xa ** prfa) = search (\ a => p (a, fb a)) (\ xa => pdec (xa, fb xa)) in
    MkDPair (xa, fb xa) $ \ (xa', xb'), pxab' => prfa xa' (prfb xa' xb' pxab')

||| The usual LPO is for Nat only
0 LPO : Type -> Type
LPO a = (f : a -> Bool) ->
        Either (x : a ** f x === True) ((x : a) -> f x === False)

0 LPO' : Type -> Type
LPO' a = (0 p : Pred a) -> Decidable p ->
         Either (x : a ** p x) ((x : a) -> Not (p x))

SearchableIsLPO : IsSearchable a -> LPO' a
SearchableIsLPO search p pdec =
  let (x ** prf) = search p pdec in
  case pdec x of
    Yes px => Left (x ** px)
    No npx => Right (\ x', px' => absurd (npx (prf x' px')))

LPOIsSearchable : LPO' a -> Inhabited a -> IsSearchable a
LPOIsSearchable lpo inh p pdec = case lpo p pdec of
  Left (x ** px) => (x ** \ _, _ => px)
  Right contra   => (inh ** \ x, px => absurd (contra x px))


-- parameters (fext : Extensionality)

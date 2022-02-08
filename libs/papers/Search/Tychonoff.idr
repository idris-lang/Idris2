||| This module is based on Todd Waugh Ambridge's blog post series
||| "Search over uniformly continuous decidable predicates on
||| infinite collections of types"
||| https://www.cs.bham.ac.uk/~txw467/tychonoff/InfiniteSearch1.html

module Search.Tychonoff

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

interface Searchable (0 a : Type) where
  search : IsSearchable a

Inhabited : Type -> Type
Inhabited a = a

SearchableIsInhabited : IsSearchable a -> Inhabited a
SearchableIsInhabited search = fst (search (\ _ => ()) (\ _ => Yes ()))

||| Finite types are trivially searchable
Searchable Bool where
  search p pdec = case pdec True of
    Yes prf   => MkDPair True $ \ _, _ => prf
    No contra => MkDPair False $ \case
      False => id
      True  => absurd . contra

||| Searchable is closed under finite sum
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

choiceAxiom :
   {0 p : a -> b -> Type} ->
   ((x : a) -> (b ** p x b)) ->
   (f : (a -> b) ** (x : a) -> p x (f x))
choiceAxiom pr = ((\ x => fst (pr x)) ** \ x => snd (pr x))

||| Searchable is closed under finite product
(Searchable a, Searchable b) => Searchable (a, b) where
  search p pdec =
    -- How cool is that use of choiceAxiom?
    let (fb ** prfb) = choiceAxiom $ \ a => search (p . (a,)) (\ b => pdec (a, b)) in
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

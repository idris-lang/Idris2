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
    (x : a ** (x0 : a ** p x0) -> p x)

interface Searchable (0 a : Type) where
  search : IsSearchable a

Inhabited : Type -> Type
Inhabited a = a

SearchableIsInhabited : IsSearchable a -> Inhabited a
SearchableIsInhabited search = fst (search (\ _ => ()) (\ _ => Yes ()))

||| Finite types are trivially searchable
Searchable Bool where
  search p pdec = case pdec True of
    Yes prf   => MkDPair True $ \ _ => prf
    No contra => MkDPair False $ \case
      (False ** pF) => pF
      (True  ** pT) => absurd (contra pT)

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
    No npx => Right (\ x', px' => absurd (npx (prf (x' ** px'))))

LPOIsSearchable : LPO' a -> Inhabited a -> IsSearchable a
LPOIsSearchable lpo inh p pdec = case lpo p pdec of
  Left (x ** px) => (x ** \ _ => px)
  Right contra   => (inh ** \ (x ** px) => absurd (contra x px))

-- parameters (fext : Extensionality)

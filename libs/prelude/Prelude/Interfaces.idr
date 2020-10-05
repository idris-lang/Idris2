module Prelude.Interfaces

import Builtin
import Prelude.Basics
import Prelude.EqOrd
import Prelude.Num
import Prelude.Ops

%default total

-------------
-- ALGEBRA --
-------------

||| Sets equipped with a single binary operation that is associative.  Must
||| satisfy the following laws:
|||
||| + Associativity of `<+>`:
|||     forall a b c, a <+> (b <+> c) == (a <+> b) <+> c
public export
interface Semigroup ty where
  (<+>) : ty -> ty -> ty

||| Sets equipped with a single binary operation that is associative, along with
||| a neutral element for that binary operation.  Must satisfy the following
||| laws:
|||
||| + Associativity of `<+>`:
|||     forall a b c, a <+> (b <+> c) == (a <+> b) <+> c
||| + Neutral for `<+>`:
|||     forall a, a <+> neutral == a
|||     forall a, neutral <+> a == a
public export
interface Semigroup ty => Monoid ty where
  neutral : ty

public export
Semigroup () where
  _ <+> _ = ()

public export
Monoid () where
  neutral = ()

public export
Semigroup Ordering where
  LT <+> _ = LT
  GT <+> _ = GT
  EQ <+> o =  o

public export
Monoid Ordering where
  neutral = EQ

public export
Semigroup b => Semigroup (a -> b) where
  (f <+> g) x = f x <+> g x

public export
Monoid b => Monoid (a -> b) where
  neutral _ = neutral


export
shiftL : Int -> Int -> Int
shiftL = prim__shl_Int

export
shiftR : Int -> Int -> Int
shiftR = prim__shr_Int

---------------------------------------------------------
-- FUNCTOR, BIFUNCTOR, APPLICATIVE, ALTERNATIVE, MONAD --
---------------------------------------------------------

||| Functors allow a uniform action over a parameterised type.
||| @ f a parameterised type
public export
interface Functor f where
  ||| Apply a function across everything of type 'a' in a parameterised type
  ||| @ f the parameterised type
  ||| @ func the function to apply
  map : (func : a -> b) -> f a -> f b

||| An infix alias for `map`, applying a function across everything of type 'a'
||| in a parameterised type.
||| @ f the parameterised type
||| @ func the function to apply
public export
(<$>) : Functor f => (func : a -> b) -> f a -> f b
(<$>) func x = map func x

||| Run something for effects, replacing the return value with a given parameter.
public export
(<$) : Functor f => b -> f a -> f b
(<$) b = map (const b)

||| Flipped version of `<$`.
public export
($>) : Functor f => f a -> b -> f b
($>) fa b = map (const b) fa

||| Run something for effects, throwing away the return value.
public export
ignore : Functor f => f a -> f ()
ignore = map (const ())

||| Bifunctors
||| @f The action of the Bifunctor on pairs of objects
public export
interface Bifunctor f where
  ||| The action of the Bifunctor on pairs of morphisms
  |||
  ||| ````idris example
  ||| bimap (\x => x + 1) reverse (1, "hello") == (2, "olleh")
  ||| ````
  |||
  bimap : (a -> c) -> (b -> d) -> f a b -> f c d
  bimap f g = mapFst f . mapSnd g

  ||| The action of the Bifunctor on morphisms pertaining to the first object
  |||
  ||| ````idris example
  ||| mapFst (\x => x + 1) (1, "hello") == (2, "hello")
  ||| ````
  |||
  mapFst : (a -> c) -> f a b -> f c b
  mapFst f = bimap f id

  ||| The action of the Bifunctor on morphisms pertaining to the second object
  |||
  ||| ````idris example
  ||| mapSnd reverse (1, "hello") == (1, "olleh")
  ||| ````
  |||
  mapSnd : (b -> d) -> f a b -> f a d
  mapSnd = bimap id

public export
mapHom : Bifunctor f => (a -> b) -> f a a -> f b b
mapHom f = bimap f f

public export
interface Functor f => Applicative f where
  pure : a -> f a
  (<*>) : f (a -> b) -> f a -> f b

public export
(<*) : Applicative f => f a -> f b -> f a
a <* b = map const a <*> b

public export
(*>) : Applicative f => f a -> f b -> f b
a *> b = map (const id) a <*> b

%allow_overloads pure
%allow_overloads (<*)
%allow_overloads (*>)

public export
interface Applicative f => Alternative f where
  empty : f a
  (<|>) : f a -> f a -> f a

public export
interface Applicative m => Monad m where
  ||| Also called `bind`.
  (>>=) : m a -> (a -> m b) -> m b

  ||| Also called `flatten` or mu.
  join : m (m a) -> m a

  -- default implementations
  (>>=) x f = join (f <$> x)
  join x = x >>= id

%allow_overloads (>>=)

public export
(>>) : (Monad m) => m a -> m b -> m b
a >> b = a >>= \_ => b

||| `guard a` is `pure ()` if `a` is `True` and `empty` if `a` is `False`.
public export
guard : Alternative f => Bool -> f ()
guard x = if x then pure () else empty

||| Conditionally execute an applicative expression.
public export
when : Applicative f => Bool -> Lazy (f ()) -> f ()
when True f = f
when False f = pure ()

---------------------------
-- FOLDABLE, TRAVERSABLE --
---------------------------

||| The `Foldable` interface describes how you can iterate over the elements in
||| a parameterised type and combine the elements together, using a provided
||| function, into a single result.
||| @ t The type of the 'Foldable' parameterised type.
public export
interface Foldable (t : Type -> Type) where
  ||| Successively combine the elements in a parameterised type using the
  ||| provided function, starting with the element that is in the final position
  ||| i.e. the right-most position.
  ||| @ func  The function used to 'fold' an element into the accumulated result
  ||| @ init  The starting value the results are being combined into
  ||| @ input The parameterised type
  foldr : (func : elem -> acc -> acc) -> (init : acc) -> (input : t elem) -> acc

  ||| The same as `foldr` but begins the folding from the element at the initial
  ||| position in the data structure i.e. the left-most position.
  ||| @ func  The function used to 'fold' an element into the accumulated result
  ||| @ init  The starting value the results are being combined into
  ||| @ input The parameterised type
  foldl : (func : acc -> elem -> acc) -> (init : acc) -> (input : t elem) -> acc
  foldl f z t = foldr (flip (.) . flip f) id t z

||| Similar to `foldl`, but uses a function wrapping its result in a `Monad`.
||| Consequently, the final value is wrapped in the same `Monad`.
public export
foldlM : (Foldable t, Monad m) => (funcM: a -> b -> m a) -> (init: a) -> (input: t b) -> m a
foldlM fm a0 = foldl (\ma,b => ma >>= flip fm b) (pure a0)

||| Combine each element of a structure into a monoid.
public export
concat : (Foldable t, Monoid a) => t a -> a
concat = foldr (<+>) neutral

||| Combine into a monoid the collective results of applying a function to each
||| element of a structure.
public export
concatMap : (Foldable t, Monoid m) => (a -> m) -> t a -> m
concatMap f = foldr ((<+>) . f) neutral

||| The conjunction of all elements of a structure containing lazy boolean
||| values.  `and` short-circuits from left to right, evaluating until either an
||| element is `False` or no elements remain.
public export
and : Foldable t => t (Lazy Bool) -> Bool
and = foldl (&&) True

||| The disjunction of all elements of a structure containing lazy boolean
||| values.  `or` short-circuits from left to right, evaluating either until an
||| element is `True` or no elements remain.
public export
or : Foldable t => t (Lazy Bool) -> Bool
or = foldl (||) False

||| The disjunction of the collective results of applying a predicate to all
||| elements of a structure.  `any` short-circuits from left to right.
public export
any : Foldable t => (a -> Bool) -> t a -> Bool
any p = foldl (\x,y => x || p y) False

||| The disjunction of the collective results of applying a predicate to all
||| elements of a structure.  `all` short-circuits from left to right.
public export
all : Foldable t => (a -> Bool) -> t a -> Bool
all p = foldl (\x,y => x && p y)  True

||| Add together all the elements of a structure.
public export
sum : (Foldable t, Num a) => t a -> a
sum = foldr (+) 0

||| Add together all the elements of a structure.
||| Same as `sum` but tail recursive.
export
sum' : (Foldable t, Num a) => t a -> a
sum' = foldl (+) 0

||| Multiply together all elements of a structure.
public export
product : (Foldable t, Num a) => t a -> a
product = foldr (*) 1

||| Multiply together all elements of a structure.
||| Same as `product` but tail recursive.
export
product' : (Foldable t, Num a) => t a -> a
product' = foldl (*) 1

||| Map each element of a structure to a computation, evaluate those
||| computations and discard the results.
public export
traverse_ : (Foldable t, Applicative f) => (a -> f b) -> t a -> f ()
traverse_ f = foldr ((*>) . f) (pure ())

||| Evaluate each computation in a structure and discard the results.
public export
sequence_ : (Foldable t, Applicative f) => t (f a) -> f ()
sequence_ = foldr (*>) (pure ())

||| Like `traverse_` but with the arguments flipped.
public export
for_ : (Foldable t, Applicative f) => t a -> (a -> f b) -> f ()
for_ = flip traverse_

||| Fold using Alternative.
|||
||| If you have a left-biased alternative operator `<|>`, then `choice` performs
||| left-biased choice from a list of alternatives, which means that it
||| evaluates to the left-most non-`empty` alternative.
|||
||| If the list is empty, or all values in it are `empty`, then it evaluates to
||| `empty`.
|||
||| Example:
|||
||| ```
||| -- given a parser expression like:
||| expr = literal <|> keyword <|> funcall
|||
||| -- choice lets you write this as:
||| expr = choice [literal, keyword, funcall]
||| ```
|||
||| Note: In Haskell, `choice` is called `asum`.
public export
choice : (Foldable t, Alternative f) => t (f a) -> f a
choice = foldr (<|>) empty

||| A fused version of `choice` and `map`.
public export
choiceMap : (Foldable t, Alternative f) => (a -> f b) -> t a -> f b
choiceMap f = foldr (\e, a => f e <|> a) empty

public export
interface (Functor t, Foldable t) => Traversable (t : Type -> Type) where
  ||| Map each element of a structure to a computation, evaluate those
  ||| computations and combine the results.
  traverse : Applicative f => (a -> f b) -> t a -> f (t b)

||| Evaluate each computation in a structure and collect the results.
public export
sequence : (Traversable t, Applicative f) => t (f a) -> f (t a)
sequence = traverse id

||| Like `traverse` but with the arguments flipped.
public export
for : (Traversable t, Applicative f) => t a -> (a -> f b) -> f (t b)
for = flip traverse


module Apply

-- These are not Biapplicatives.  Those are in Data.Biapplicative

infixl 4 <<$>>, <<&>>, <<.>>, <<., .>>, <<..>>

||| Primarily used to make the definitions of bilift2 and bilift3 pretty
|||
||| ```idris example
||| bimap const const <<$>> (1, 2) <<.>> (3, 4) == (1, 2)
||| ```
|||
export
(<<$>>) : (a -> b) -> a -> b
(<<$>>) = id

||| <<$>> with the arguments reversed
|||
||| ```idris example
||| (1, 2) <<&>> bimap const const <<.>> (3, 4) == (1, 2)
||| ```
|||
(<<&>>) : a -> (a -> b) -> b
(<<&>>) = flip id

||| Biapplys (not to be confused with Biapplicatives)
||| @p The action of the Biapply on pairs of objects
public export
interface Bifunctor p => Biapply (p : Type -> Type -> Type) where

  ||| Applys a Bifunctor of functions to another Bifunctor of the same type
  |||
  ||| ````idris example
  ||| (reverse, (\x => x + 1)) <<.>> ("hello", 1) == ("olleh", 2)
  ||| ````
  |||
  (<<.>>) : p (a -> b) (c -> d) -> p a c -> p b d

  ||| Given two Bifunctors, sequences them leftwards
  |||
  ||| ````idris example
  ||| ("hello", 1) <<. ("goodbye", 2) == ("hello", 1)
  ||| ````
  |||
  (<<.) : p a b -> p c d -> p a b
  a <<. b = bimap const const <<$>> a <<.>> b

  ||| Given two Bifunctors, sequences them rightwards
  |||
  ||| ````idris example
  ||| ("hello", 1) <<. ("goodbye", 2) == ("goodbye", 2)
  ||| ````
  |||
  (.>>) : p a b -> p c d -> p c d
  a .>> b = bimap (const id) (const id) <<$>> a <<.>> b

||| Lifts a pair of binary functions into a Bifunctor
|||
||| ````idris example
||| bilift2 (++) (+) ("hello", 1) ("goodbye", 2) == ("hellogoodbye", 3)
||| ````
|||
bilift2 : Biapply p => (a -> b -> c) -> (d -> e -> f) -> p a d -> p b e -> p c f
bilift2 f g a b = bimap f g <<$>> a <<.>> b

||| Lifts a pair of ternary functions into a Bifunctor
|||
||| ````idris example
||| bilift3 (\x,y,z => x ++ (y ++ z)) (\x,y,z => x + (y + z))
|||         ("hello", 1) ("goodbye", 2) ("hello again", 3) ==
||| ("hellogoodbyehello again", 6)
||| ````
|||
bilift3 : Biapply p => (a -> b -> c -> d) -> (e -> f -> g -> h)
        -> p a e -> p b f -> p c g -> p d h
bilift3 f g a b c = bimap f g <<$>> a <<.>> b <<.>> c

||| Applies the second of two Bifunctors to the first
|||
||| ````idris example
||| ("hello", 1) <<..>> (reverse, (\x => x + 1)) == ("olleh", 2)
||| ````
|||
(<<..>>): Biapply p => p a c -> p (a -> b) (c -> d) -> p b d
(<<..>>) = flip (<<.>>)

implementation Biapply Pair where
  (f, g) <<.>> (a, b) = (f a, g b)

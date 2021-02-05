module Biapplicative

import Apply

infixl 4 <<*>>, <<*, *>>, <<**>>

||| Biapplicatives
||| @p the action of the Biapplicative on pairs of objects
public export
interface Bifunctor p => Biapplicative p where -- (p : Type -> Type -> Type) where

  ||| Lifts two values into a Biapplicative
  |||
  ||| ````idris example
  ||| bipure 1 "hello" = (1, "hello")
  ||| ````
  |||
  bipure : a -> b -> p a b

  ||| Applies a Biapplicative of functions to a second Biapplicative
  |||
  ||| ````idris example
  ||| ( (\x => x + 1), reverse ) <<*>> (1, "hello") == (2, "olleh")
  ||| ````
  |||
  (<<*>>) : p (a -> b) (c -> d) -> p a c -> p b d

  ||| Sequences two Biapplicatives rightwards
  |||
  ||| ````idris example
  ||| (1, "hello") *>> (2, "goodbye") = (2, "goodbye")
  ||| ````
  |||
  (*>>) : p a b -> p c d -> p c d
  a *>> b = bimap (const id) (const id) <<$>> a <<*>> b

  ||| Sequences two Biapplicatives leftwards
  |||
  ||| ````idris example
  ||| (1, "hello") <<* (2, "goodbye") = (1, "hello")
  ||| ````
  |||
  (<<*) : p a b -> p c d -> p a b
  a <<* b = bimap const const <<$>> a <<*>> b

||| Applies the second of two Biapplicatives to the first
|||
||| ````idris example
||| (1, "hello") <<**>> ( (\x => x + 1), reverse ) == (2, "olleh")
||| ````
|||
export
(<<**>>) : Biapplicative p => p a c -> p (a -> b) (c -> d) -> p b d
(<<**>>) = flip (<<*>>)

export
biliftA2 : Biapplicative p => (a -> b -> c) ->
                              (d -> e -> f) -> p a d -> p b e -> p c f
biliftA2 f g a b = bimap f g <<$>> a <<*>> b

export
biliftA3 : Biapplicative p =>
  (a -> b -> c -> d) -> (e -> f -> g -> h) -> p a e -> p b f -> p c g -> p d h
biliftA3 f g a b c = bimap f g <<$>> a <<*>> b <<*>> c

public export
implementation Biapplicative Pair where
  bipure a b          = (a, b)
  (f, g) <<*>> (a, b) = (f a, g b)

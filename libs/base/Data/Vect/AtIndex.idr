||| Indexing Vectors.
|||
||| `Elem` proofs give existential quantification that a given element
||| *is* in the list, but not where in the list it is!  Here we give a
||| predicate that presents proof that a given index of a vector,
||| given by a `Fin` instance, will return a certain element.
|||
||| Two decidable decision procedures are presented:
|||
||| 1. Check that a given index points to the provided element in the
|||    presented vector.
|||
||| 2. Find the element at the given index in the presented vector.
module Data.Vect.AtIndex

import Data.Vect
import Decidable.Equality

%default total

public export
data AtIndex : (idx : Fin n)
            -> (xs  : Vect n type)
            -> (x   : type)
                   -> Type
  where
    Here : AtIndex FZ (x::xs) x

    There : (later : AtIndex     rest      xs  x)
                  -> AtIndex (FS rest) (y::xs) x

namespace Check
  public export
  elemDiffers : (y = x -> Void)
              -> AtIndex FZ (y :: xs) x
              -> Void
  elemDiffers f Here
    = f Refl

  public export
  elemNotInRest : (AtIndex z xs x -> Void)
               ->  AtIndex (FS z) (y :: xs) x
               ->  Void
  elemNotInRest f (There later)
    = f later

  ||| Is the element at the given index?
  |||
  public export
  index : DecEq type
       => (idx : Fin n)
       -> (x   : type)
       -> (xs  : Vect n type)
              -> Dec (AtIndex idx xs x)

  index FZ _ [] impossible
  index (FS y) _ [] impossible

  index FZ x (y :: xs) with (decEq y x)
    index FZ x (x :: xs) | (Yes Refl)
      = Yes Here
    index FZ x (y :: xs) | (No contra)
      = No (elemDiffers contra)

  index (FS z) x (y :: xs) with (Check.index z x xs)
    index (FS z) x (y :: xs) | (Yes prf)
      = Yes (There prf)
    index (FS z) x (y :: xs) | (No contra)
      = No (elemNotInRest contra)

namespace Find
  public export
  elemNotInRest : (DPair type (AtIndex     x        xs)  -> Void)
               ->  DPair type (AtIndex (FS x) (y :: xs)) -> Void

  elemNotInRest f (MkDPair i (There later))
    = f (MkDPair i later)

  ||| What is the element at the given index?
  |||
  public export
  index : DecEq type
       => (idx : Fin n)
       -> (xs  : Vect n type)
              -> Dec (DPair type (AtIndex idx xs))
  index FZ (x :: xs)
    = Yes (MkDPair x Here)

  index (FS x) (y :: xs) with (Find.index x xs)
    index (FS x) (y :: xs) | (Yes (MkDPair i idx))
      = Yes (MkDPair i (There idx))
    index (FS x) (y :: xs) | (No contra) = No (elemNotInRest contra)

-- [ EOF ]

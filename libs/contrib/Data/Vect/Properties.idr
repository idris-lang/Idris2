||| Additional properties and lemmata to do with Vect
|||
||| Tabulation gives a bijection between functions `f : Fin n -> a`
||| (up to extensional equality) and vectors `tabulate f : Vect n a`.
module Data.Vect.Properties

import Data.Vect
import Data.Vect.Elem
import Data.Fin

import Syntax.PreorderReasoning

||| Vectors are uniquely determined by their elements
export
vectorExtensionality
  : (xs, ys : Vect n a) -> (ext : (i : Fin n) -> index i xs = index i ys)
 -> xs = ys
vectorExtensionality    []        []     ext = Refl
vectorExtensionality (x :: xs) (y :: ys) ext =
  cong2 (::)
        (ext FZ)
        (vectorExtensionality xs ys (\i => ext (FS i)))

||| Extensionally equivalent functions tabulate to the same vector
export
tabulateExtensional
  : {n : Nat} -> (f, g : Fin n -> a) -> (ext : (i : Fin n) -> f i = g i)
 -> tabulate f = tabulate g
tabulateExtensional {n = 0  } f g ext = Refl
tabulateExtensional {n = S n} f g ext =
  rewrite ext FZ in
  cong (g FZ ::) (tabulateExtensional (f . FS) (g . FS) (\ i => ext $ FS i))

||| Taking an index amounts to applying the tabulated function
export
indexTabulate : {n : Nat} -> (f : Fin n -> a) -> (i : Fin n) -> index i (tabulate f) = f i
indexTabulate f  FZ    = Refl
indexTabulate f (FS i) = indexTabulate (f . FS) i

||| The empty vector represents the unique function `Fin 0 -> a`
export
emptyInitial : (v : Vect 0 a) -> v = []
emptyInitial [] = Refl

||| Recall an element by its position, as we may not have the element
||| at runtime
public export
recallElem : {xs : Vect n a} -> x `Elem` xs -> a
recallElem {xs = x :: _ }  Here         = x
recallElem {xs = _ :: xs} (There later) = recallElem later

||| Recalling by a position of `x` does yield `x`
export
recallElemSpec : (pos : x `Elem` xs) -> recallElem pos = x
recallElemSpec  Here         = Refl
recallElemSpec (There later) = recallElemSpec later

||| map-fusion property for vectors up to function extensionality
export
mapFusionVect : (f : b -> c) -> (g : a -> b) -> (xs : Vect n a)
  -> map f (map g xs) = map (f . g) xs
mapFusionVect f g    []     = Refl
mapFusionVect f g (x :: xs) = cong (f $ g x ::) $ mapFusionVect f g xs

||| `index i : Vect n a -> a` is a natural transformation
export
indexNaturality : (i : Fin n) -> (f : a -> b) -> (xs : Vect n a)
  -> index i (map f xs) = f (index i xs)
indexNaturality  FZ    f (x :: xs) = Refl
indexNaturality (FS x) f (_ :: xs)  = indexNaturality x f xs

||| Replication tabulates the constant function
export
indexReplicate : (i : Fin n) -> (x : a)
  -> index i (replicate n x) = x
indexReplicate  FZ    x = Refl
indexReplicate (FS i) x = indexReplicate i x

||| `range` tabulates the identity function (by definition)
export
indexRange : (i : Fin n) -> index i (range {len = n}) === i
indexRange i = irrelevantEq $ indexTabulate id i

||| Inductive step auxiliary lemma for indexTranspose
indexZipWith_Cons : (i : Fin n) -> (xs : Vect n a) -> (xss : Vect n (Vect m a))
  -> index i (zipWith (::) xs xss)
  = (index i xs)       :: (index i xss)
indexZipWith_Cons  FZ    (x :: _ ) (xs:: _  ) = Refl
indexZipWith_Cons (FS i) (_ :: xs) (_ :: xss) = indexZipWith_Cons i xs xss

||| The `i`-th vector in a transposed matrix is the vector of `i`-th components
export
indexTranspose : (xss : Vect m (Vect n a)) -> (i : Fin n)
  -> index i (transpose xss) = map (index i) xss
indexTranspose     []      i = indexReplicate i []
indexTranspose (xs :: xss) i = Calc $
  |~ index i (transpose (xs :: xss))
  ~~ index i (zipWith (::) xs (transpose xss))  ...(Refl)
  ~~ index i xs :: index i (transpose xss)      ...(indexZipWith_Cons i xs (transpose xss))
  ~~ index i xs :: map (index i) xss            ...(cong (index i xs ::)
                                                         $ indexTranspose xss i)

{- ------------------ foldr's universal property -------------------------

   foldr is the unique solution to the equation:

     h f e [] = e
     h f e (x :: xs) = x `h` (foldr f e xs)

   (This fact is called 'the universal property of foldr'.)

   Since the prelude defines foldr tail-recursively, this fact isn't immediate
   and we need some lemmata to prove it.

   ------------------------------------------------------------------------}

||| A function H : forall n. Vect n A -> B preserving the structure of vectors over A
public export
record VectHomomorphismProperty {0 A, B : Type} (F : A -> B -> B) (E : B) (H : forall n . Vect n A -> B) where
  constructor ShowVectHomomorphismProperty
  nil  : H [] = E
  cons : {0 n : Nat} -> (x : A) -> (xs : Vect n A) -> H (x :: xs) = x `F` (H xs)

||| There is an extensionally unique function preserving the vector structure
export
nilConsInitiality :
     (f : a -> b -> b) -> (e : b)
  -> (h1, h2 : forall n . Vect n a -> b)
  -> (prf1 : VectHomomorphismProperty f e h1)
  -> (prf2 : VectHomomorphismProperty f e h2)
  -> (xs : Vect n a) -> h1 xs = h2 xs
nilConsInitiality f e h1 h2 prf1 prf2 [] = Calc $
  |~ h1 []
  ~~ e     ...(prf1.nil)
  ~~ h2 [] ...(sym prf2.nil)

nilConsInitiality f e h1 h2 prf1 prf2 (x :: xs) = Calc $
  |~ h1 (x :: xs)
  ~~ (x `f` (h1 xs)) ...(prf1.cons _ _)
  ~~ (x `f` (h2 xs)) ...(cong (x `f`) $ nilConsInitiality f e h1 h2 prf1 prf2 xs)
  ~~ h2 (x :: xs) ...(sym $ prf2.cons _ _)

||| extensionality is a congruence with respect to Data.Vect.foldrImpl
foldrImplExtensional :
  (f : a -> b -> b) -> (e : b)
  -> (go1, go2 : b -> b)
  -> ((y : b) -> go1 y = go2 y)
  -> (xs : Vect n a)
  -> foldrImpl f e go1 xs = foldrImpl f e go2 xs
foldrImplExtensional f e go1 go2 ext [] = ext e
foldrImplExtensional f e go1 go2 ext (x :: xs) =
  foldrImplExtensional f e _ _
  (\y => ext (f x y))
  xs

||| foldrImpl f e x : (b -> -) -> - is natural
foldrImplNaturality : (f : a -> b -> b) -> (e : b) -> (xs : Vect n a) -> (go1, go2 : b -> b)
  -> foldrImpl f e (go1 . go2) xs = go1 (foldrImpl f e go2 xs)
foldrImplNaturality f e    []     go1 go2 = Refl
foldrImplNaturality f e (x :: xs) go1 go2 = foldrImplNaturality f e xs go1 (go2 . (f x))

||| Our tail-recursive foldr preserves the vector structure
export
foldrVectHomomorphism : VectHomomorphismProperty f e (foldr f e)
foldrVectHomomorphism = ShowVectHomomorphismProperty
  { nil  = Refl
  , cons = \x, xs => Calc $
    |~ foldr f e (x :: xs)
    ~~ foldrImpl f e (id . (f x)) xs ...(Refl)
    ~~ foldrImpl f e ((f x) . id) xs ...(foldrImplExtensional f e _ _ (\y => Refl) xs)
    ~~ f x (foldrImpl f e id xs)     ...(foldrImplNaturality f e xs (f x) _)
    ~~ f x (foldr f e xs)            ...(Refl)
  }

||| foldr is the unique function preserving the vector structure
export
foldrUniqueness : (h : forall n . Vect n a -> b) -> VectHomomorphismProperty f e h -> (xs : Vect n a) -> h xs = foldr f e xs
foldrUniqueness {f} h prf xs = irrelevantEq $
  nilConsInitiality f e h (foldr f e) prf foldrVectHomomorphism xs

||| The content of this module is based on the paper
||| Applications of Applicative Proof Search
||| by Liam O'Connor

module Search.HDecidable

import Data.List.Quantifiers
import Data.So

%default total

||| Half a decider
public export
record HDec (a : Type) where
  constructor MkHDec
  isTrue   : Bool
  evidence : So isTrue -> a

public export
yes : a -> HDec a
yes = MkHDec True . const

public export
no : HDec a
no = MkHDec False absurd

public export
Functor HDec where
  map f (MkHDec b prf) = MkHDec b (f . prf)

public export
Applicative HDec where
  pure = yes
  MkHDec bf prff <*> MkHDec bx prfx
    = MkHDec (bf && bx) $ \ wit =>
        let (witf, witx) = soAnd {b = Delay bx} wit in
        prff witf (prfx witx)

public export
Alternative HDec where
  empty = no
  p@(MkHDec True _) <|> _ = p
  _ <|> q = q

public export
Monad HDec where
  MkHDec True x >>= f = f (x Oh)
  _ >>= _ = no

public export
toMaybe : HDec a -> Maybe a
toMaybe (MkHDec True p) = Just (p Oh)
toMaybe (MkHDec False _) = Nothing

public export
fromDec : Dec a -> HDec a
fromDec (Yes p) = yes p
fromDec (No _) = no

public export
interface AnHDec (0 t : Type -> Type) where
  toHDec : t a -> HDec a

public export AnHDec Dec where toHDec = fromDec
public export AnHDec HDec where toHDec = id

public export
(&&) : (AnHDec l, AnHDec r) => l a -> r b -> HDec (a, b)
p && q = [| (toHDec p, toHDec q) |]

public export
(||) : (AnHDec l, AnHDec r) => l a -> r b -> HDec (Either a b)
p || q = [| Left (toHDec p) |] <|> [| Right (toHDec q) |]

infixr 3 ==>

public export
(==>) : (AnHDec l, AnHDec r) => l (Not a) -> r b -> HDec (a -> b)
p ==> q = [| contra (toHDec p) |] <|> [| const (toHDec q) |] where
  contra : Not a -> a -> b
  contra na a = void (na a)

public export
any : AnHDec l => (xs : List a) -> ((x : a) -> l (p x)) -> HDec (Any p xs)
any [] p = no
any (x :: xs) p = [| Here (toHDec (p x)) |] <|> [| There (any xs p) |]

public export
all : AnHDec l => (xs : List a) -> ((x : a) -> l (p x)) -> HDec (All p xs)
all [] p = yes []
all (x :: xs) p = [| toHDec (p x) :: all xs p |]

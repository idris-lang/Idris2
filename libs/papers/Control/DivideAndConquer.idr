||| The content of this module is based on the paper
||| A Type-Based Approach to Divide-And-Conquer Recursion in Coq
||| by Pedro Abreu, Benjamin Delaware, Alex Hubers, Christa Jenkins,
||| J. Garret Morris, and Aaron Stump
||| https://doi.org/10.1145/3571196
|||
||| The original paper relies on Coq's impredicative Set axiom,
||| something we don't have access to in Idris 2. We can however
||| reproduce the results by ignoring the type levels

module Control.DivideAndConquer

%default total

namespace Section4Sub1

  public export
  data ListF : (a, x : Type) -> Type where
    Nil : ListF a x
    (::) : a -> x -> ListF a x

  lengthAlg : ListF a Nat -> Nat
  lengthAlg [] = 0
  lengthAlg (_ :: n) = S n

  public export
  Functor (ListF a) where
    map f [] = []
    map f (x :: xs) = x :: f xs

namespace Section6Sub1

  public export
  -- Only accepted because there is currently no universe check
  data Mu : (Type -> Type) -> Type where
    MkMu : forall r. (r -> Mu f) -> f r -> Mu f

  public export
  inMu : f (Mu f) -> Mu f
  inMu = MkMu id

  public export
  outMu : Functor f => Mu f -> f (Mu f)
  outMu (MkMu f d) = f <$> d

  public export
  fold : Functor f => (f a -> a) -> Mu f -> a
  fold alg (MkMu f r) = alg (assert_total (fold alg . f <$> r))

namespace Section4Sub1

  list : Type -> Type
  list = Mu . ListF

  namespace Smart

    Nil : list a
    Nil = inMu []

    (::) : a -> list a -> list a
    x :: xs = inMu (x :: xs)

    fromList : List a -> list a
    fromList = foldr (::) []

    toList : list a -> List a
    toList = fold $ \case
      [] => []
      (x :: xs) => x :: xs

namespace Section4Sub2

  public export
  KAlg : Type
  KAlg = (Type -> Type) -> Type

  public export
  0 Mono : (KAlg -> KAlg) -> Type
  Mono f
    = forall a, b.
      (forall x.   a x ->   b x) ->
      (forall x. f a x -> f b x)

  public export
  data Mu : (KAlg -> KAlg) -> KAlg where
    MkMu : (forall x. a x -> Mu f x) ->
           (forall x. f a x -> Mu f x)

  public export
  inMu : f (Mu f) x -> Mu f x
  inMu = MkMu id

  public export
  outMu : Mono f -> Mu f x -> f (Mu f) x
  outMu m (MkMu f d) = m f d

  parameters (0 f : Type -> Type)

    public export
    0 FoldT : KAlg -> Type -> Type
    FoldT a r
      = forall x.
        Functor x =>
        a x -> r -> x r

    public export
    0 SAlgF : KAlg -> (Type -> Type) -> Type
    SAlgF a x
      = forall p, r.
        (r -> p) ->
        FoldT a r ->
        (f r -> p) ->
        (r -> x r) ->
        f r -> x p


    public export
    0 SAlg : (Type -> Type) -> Type
    SAlg = Mu SAlgF

    public export
    0 AlgF : KAlg -> (Type -> Type) -> Type
    AlgF a x
      = forall r.
        FoldT a r ->
        FoldT SAlg r ->
        (r -> x r) ->
        f r -> x r

    public export
    0 Alg : (Type -> Type) -> Type
    Alg = Mu AlgF

    public export
    inSAlg : SAlgF SAlg x -> SAlg x
    inSAlg = inMu

    public export
    monoSAlgF : Mono SAlgF
    monoSAlgF f salg up sfo = salg up (sfo . f)

    public export
    outSAlg : SAlg x -> SAlgF SAlg x
    outSAlg = outMu monoSAlgF

    public export
    inAlg : AlgF Alg x -> Alg x
    inAlg = inMu

    public export
    monoAlgF : Mono AlgF
    monoAlgF f alg fo = alg (fo . f)

    public export
    outAlg : Alg x -> AlgF Alg x
    outAlg = outMu monoAlgF

namespace Section6Sub2

  parameters (0 f : Type -> Type)

    public export
    0 DcF : Type -> Type
    DcF a = forall x. Functor x => Alg f x -> x a

    public export
    functorDcF : Functor DcF
    functorDcF = MkFunctor $ \ f, dc, alg => map f (dc alg)

    public export
    0 Dc : Type
    Dc = Mu DcF

    public export
    fold : FoldT f (Alg f) Dc
    fold alg dc = outMu @{functorDcF} dc alg

    public export
    record RevealT (x : Type -> Type) (r : Type) where
      constructor MkRevealT
      runRevealT : (r -> Dc) -> x Dc

    public export %hint
    functorRevealT : Functor (RevealT x)
    functorRevealT = MkFunctor $ \ f, t =>
      MkRevealT (\ g => runRevealT t (g . f))

    public export
    promote : Functor x => SAlg f x -> Alg f (RevealT x)
    promote salg
      = inAlg f $ \ fo, sfo, rec, fr =>
        MkRevealT $ \ reveal =>
        let abstIn := \ fr => inMu (\ alg => reveal <$> outAlg f alg fo sfo (fo alg) fr) in
        outSAlg f salg reveal sfo abstIn (sfo salg) fr

    public export
    sfold : FoldT f (SAlg f) Dc
    sfold salg dc = runRevealT (fold (promote salg) dc) id

    public export
    inDc : f Dc -> Dc
    inDc d = inMu (\ alg => outAlg f alg fold sfold (fold alg) d)

    out : Functor f => FoldT f (SAlg f) r -> r -> f r
    out sfo = sfo (inSAlg f (\ up, _, _, _ => map up))

namespace Section5Sub1

  public export
  0 list : Type -> Type
  list a = Dc (ListF a)

  namespace Smart

    public export
    Nil : list a
    Nil = inDc (ListF a) []

    public export
    (::) : a -> list a -> list a
    x :: xs = inDc (ListF a) (x :: xs)

    public export
    fromList : List a -> list a
    fromList = foldr (::) []

  public export
  0 SpanF : Type -> Type -> Type
  SpanF a x = (List a, x)

  SpanSAlg : (a -> Bool) -> SAlg (ListF a) (SpanF a)
  SpanSAlg p = inSAlg (ListF a) $ \up, sfo, abstIn, span, xs =>
    case xs of
      [] => ([], abstIn xs)
      (x :: xs') =>
        if p x
        then let (r, s) = span xs' in (x :: r, up s)
        else ([], abstIn xs)

  export
  spanr : FoldT (ListF a) (SAlg (ListF a)) r ->
          (a -> Bool) -> (xs : r) -> SpanF a r
  spanr sfo p xs = sfo (SpanSAlg p) @{MkFunctor mapSnd} xs

  breakr : FoldT (ListF a) (SAlg (ListF a)) r ->
           (a -> Bool) ->  (xs : r) -> SpanF a r
  breakr sfo p = spanr sfo (not . p)

  WordsByAlg : (a -> Bool) -> Alg (ListF a) (const (List (List a)))
  WordsByAlg p = inAlg (ListF a) $ \ fo, sfo, wordsBy, xs =>
    case xs of
      [] => []
      (hd :: tl) =>
        if p hd
        then wordsBy tl
        else
          let (w, rest) = breakr sfo p tl in
          (hd :: w) :: wordsBy rest

  wordsBy : (a -> Bool) -> (xs : List a) -> List (List a)
  wordsBy p = fold (ListF a) @{MkFunctor (const id)} (WordsByAlg p) . fromList

namespace Section5Sub3

  data NatF x = Z | S x

  0 nat : Type
  nat = Dc NatF

  fromNat : Nat -> Section5Sub3.nat
  fromNat Z = inDc NatF Z
  fromNat (S n) = inDc NatF (S (fromNat n))

  toNat : Section5Sub3.nat -> Nat
  toNat = fold NatF @{MkFunctor (const id)} idAlg where

    idAlg : Alg NatF (const Nat)
    idAlg = inAlg NatF $ \ fo, sfo, toNat, n =>
      case n of
        Z => Z
        S n' => S (toNat n')

  zeroSAlg : SAlg NatF Prelude.id
  zeroSAlg = inSAlg NatF $ \ up, sfo, abstIn, zero, n =>
    case n of
      Z => abstIn n
      S p => up (zero (zero p))

  export
  zero : Nat -> Nat
  zero = toNat . sfold NatF @{MkFunctor id} zeroSAlg . fromNat

namespace Section5Sub3

  data TreeF a x = Node a (List x)

  0 tree : Type -> Type
  tree a = Dc (TreeF a)

  node : a -> List (tree a) -> tree a
  node n ts = inDc (TreeF a) (Node n ts)

  mirrorAlg : SAlg (TreeF a) Prelude.id
  mirrorAlg = inSAlg (TreeF a) $ \ up, sfo, abstIn, mirror, t =>
    case t of Node a ts => abstIn (Node a $ map mirror (reverse ts))

  mirror : tree a -> tree a
  mirror = sfold (TreeF a) @{MkFunctor id} mirrorAlg

namespace Section5Sub4

  0 MappedT : (a, b : Type) -> Type
  MappedT a b = forall r. FoldT (ListF a) (SAlg (ListF a)) r -> a -> r -> (b, r)

  MapThroughAlg : MappedT a b -> Alg (ListF a) (const (List b))
  MapThroughAlg f = inAlg (ListF a) $ \fo, sfo, mapThrough, xs =>
    case xs of
      [] => []
      hd :: tl =>
        let (b, rest) = f sfo hd tl in
        b :: mapThrough rest

  mapThrough : MappedT a b -> list a -> List b
  mapThrough f = fold (ListF a) (MapThroughAlg f) @{MkFunctor (const id)}

  compressSpan : Eq a => MappedT a (Nat, a)
  compressSpan sfo hd tl
    = let (pref, rest) = spanr sfo (hd ==) tl in
      ((S (length pref), hd), rest)

  runLengthEncoding : Eq a => List a -> List (Nat, a)
  runLengthEncoding = mapThrough compressSpan . fromList

namespace Section5Sub5

  K : Type -> Type
  K t = t -> Bool

  MatchT : Type -> Type
  MatchT t = K t -> Bool

  data Regex = Zero | Exact Char | Sum Regex Regex | Cat Regex Regex | Plus Regex

  matchi : (t -> Regex -> MatchT t) -> Regex -> Char -> t -> MatchT t
  matchi matcher Zero c cs k = False
  matchi matcher (Exact c') c cs k = (c == c') && k cs
  matchi matcher (Sum r1 r2) c cs k = matchi matcher r1 c cs k || matchi matcher r2 c cs k
  matchi matcher (Cat r1 r2) c cs k = matchi matcher r1 c cs (\ cs => matcher cs r2 k)
  matchi matcher (Plus r) c cs k = matchi matcher r c cs (\ cs => k cs || matcher cs (Plus r) k)

  MatcherF : Type -> Type
  MatcherF t = Regex -> MatchT t

  functorMatcherF : Functor MatcherF
  functorMatcherF = MkFunctor (\ f, t, r, p => t r (p . f))

  MatcherAlg : Alg (ListF Char) MatcherF
  MatcherAlg = inAlg (ListF Char) $ \ fo, sfo, matcher, s =>
    case s of
      [] =>  \ r, k => False
      (c :: cs) => \ r => matchi matcher r c cs

  match : Regex -> String -> Bool
  match r str = fold (ListF Char) MatcherAlg @{functorMatcherF} chars r isNil

    where
      isNil : Mu (DcF (ListF Char)) -> Bool
      isNil = fold (ListF Char) {x = const Bool} @{MkFunctor (const id)}
            $ inAlg (ListF Char)
            $ \fo, sfo, rec, xs => case xs of
              Nil => True
              (_ :: _) => False

      chars : Mu (DcF (ListF Char))
      chars = fromList (unpack str)

  export
  matchExample : Bool
  matchExample = match (Plus $ Cat (Sum (Exact 'a') (Exact 'b')) (Exact 'a')) "aabaaaba"

namespace Section5Sub6

  parameters {0 a : Type} (ltA : a -> a -> Bool)

    0 PartF : Type -> Type
    PartF x = a -> (x, x)

    PartSAlg : SAlg (ListF a) PartF
    PartSAlg = inSAlg (ListF a) $ \up, sfo, abstIn, partition, d, pivot => case d of
      [] => let xs = abstIn d in (xs, xs)
      x :: xs => let (l, r) = partition xs pivot in
                 if ltA x pivot then (abstIn (x :: l), up r)
                 else (up l, abstIn (x :: r))

    partr : (sfo : FoldT (ListF a) (SAlg (ListF a)) r) -> r -> a -> (r, r)
    partr sfo = sfo @{MkFunctor $ \ f, p, x => bimap f f (p x)} PartSAlg

    QuickSortAlg : Alg (ListF a) (const (List a))
    QuickSortAlg = inAlg (ListF a) $ \ fo, sfo, qsort, xs => case xs of
      [] => []
      p :: xs => let (l, r) = partr sfo xs p in
                 qsort l ++ p :: qsort r

    quicksort : List a -> List a
    quicksort = fold (ListF a) QuickSortAlg @{MkFunctor (const id)} . fromList

  export
  sortExample : String -> String
  sortExample = pack . quicksort (<=) . unpack

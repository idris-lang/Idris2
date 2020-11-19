-- This module is based on the following papers:

-- Categories of Containers
-- Abbott, Altenkirch, Ghani


module Data.Container

%default total

namespace Container

  public export
  record Container where
    constructor MkContainer
    Shape : Type
    Position : Shape -> Type

  public export
  Extension : Container -> Type -> Type
  Extension c x = (s : Shape c ** Position c s -> x)

  public export
  map : (x -> y) -> Extension c x -> Extension c y
  map f (s ** p) = (s ** f . p)

namespace Const

  public export
  Const : Type -> Container
  Const k = MkContainer k (const Void)

  export
  toConst : k -> Extension (Const k) x
  toConst v = (v ** absurd)

  export
  fromConst : Extension (Const k) x -> k
  fromConst (v ** _) = v

namespace Identity

  public export
  Identity : Container
  Identity = MkContainer () (\ () => ())

  export
  toIdentity : x -> Extension Identity x
  toIdentity v = (() ** const v)

  export
  fromIdentity : Extension Identity x -> x
  fromIdentity (() ** chld) = chld ()

namespace Compose

  public export
  Compose : (d, c : Container) -> Container
  Compose d c = MkContainer (Extension d (Shape c)) (\ (shp ** chld) => (p : Position d shp ** Position c (chld p)))

  export
  toCompose : (Extension d . Extension c) x -> Extension (Compose d c) x
  toCompose (shp1 ** chld) = ((shp1 ** \ p => fst (chld p)) ** \ (p ** q) => snd (chld p) q)

  export
  fromCompose : Extension (Compose d c) x -> (Extension d . Extension c) x
  fromCompose ((shp1 ** shp2) ** chld) = (shp1 ** \ p => (shp2 p ** \ q => chld (p ** q)))

namespace Sum

  public export
  Sum : (c, d : Container) -> Container
  Sum c d = MkContainer (Either (Shape c) (Shape d)) (either (Position c) (Position d))

  export
  toSum : Either (Extension c x) (Extension d x) -> Extension (Sum c d) x
  toSum (Left (shp ** chld)) = (Left shp ** chld)
  toSum (Right (shp ** chld)) = (Right shp ** chld)

  export
  fromSum : Extension (Sum c d) x -> Either (Extension c x) (Extension d x)
  fromSum (Left shp ** chld) = Left (shp ** chld)
  fromSum (Right shp ** chld) = Right (shp ** chld)

namespace Pair

  public export
  Pair : (c, d : Container) -> Container
  Pair c d = MkContainer (Shape c, Shape d) (\ (p, q) => Either (Position c p) (Position d q))

  export
  toPair : (Extension c x, Extension d x) -> Extension (Pair c d) x
  toPair ((shp1 ** chld1), (shp2 ** chld2)) = ((shp1, shp2) ** either chld1 chld2)

  export
  fromPair : Extension (Pair c d) x -> (Extension c x, Extension d x)
  fromPair ((shp1, shp2) ** chld) = ((shp1 ** chld . Left), (shp2 ** chld . Right))

namespace Exponential

  public export
  Exponential : Type -> Container -> Container
  Exponential k c = MkContainer (k -> Shape c) (\ p => (v : k ** Position c (p v)))

  export
  toExponential : (k -> Extension c x) -> Extension (Exponential k c) x
  toExponential f = (fst . f ** \ (v ** p) => snd (f v) p)

  export
  fromExponential : Extension (Exponential k c) x -> (k -> Extension c x)
  fromExponential (shp ** chld) k = (shp k ** \ p => chld (k ** p))

namespace Morphism

  public export
  record Morphism (c, d : Container) where
    constructor MkMorphism
    shapeMorphism : Shape c -> Shape d
    positionMorphism : {s : Shape c} -> Position d (shapeMorphism s) -> Position c s

  public export
  Extension : Morphism c d -> Extension c x -> Extension d x
  Extension phi (s ** p) = (shapeMorphism phi s ** p . positionMorphism phi)

namespace Initial

  public export
  data W : Container -> Type where
    MkW : Extension c (W c) -> W c

  export
  map : Morphism c d -> W c -> W d
  map f (MkW (shp ** chld)) = MkW $ Extension f (shp ** \ p => map f (chld p))
  --  Container.map inlined because of ---------^
  --  termination checking

  export
  foldr : (Extension c x -> x) -> W c -> x
  foldr alg (MkW (shp ** chld)) = alg (shp ** \ p => foldr alg (chld p))

  export
  para : (Extension c (x, W c) -> x) -> W c -> x
  para alg (MkW (shp ** chld)) = alg (shp ** \ p => let w = chld p in (para alg w, w))

namespace Monad

  public export
  record Free (c : Container) (x : Type) where
    constructor MkFree
    runFree : W (Sum c (Const x))

  export
  pure : x -> Free c x
  pure x = MkFree $ MkW (toSum {d = Const _} (Right (toConst x)))

  export
  (>>=) : Free c x -> (x -> Free c y) -> Free c y
  (>>=) (MkFree mx) k =
    let alg : Either (Extension c (Free c y)) (Extension (Const x) (Free c y)) -> Free c y
            := either (\ v => MkFree $ MkW (Left (fst v) ** runFree . snd v)) (k . fromConst)
    in foldr (alg . fromSum {d = Const _}) mx

namespace Final

  public export
  data M : Container -> Type where
    MkM : Extension c (Inf (M c)) -> M c

  export
  unfoldr : (s -> Extension c s) -> s -> M c
  unfoldr next seed =
    let (shp ** chld) = next seed in
    MkM (shp ** \ p => unfoldr next (chld p))


namespace Comonad

  public export
  record Cofree (c : Container) (x : Type) where
    constructor MkCofree
    runCofree : M (Pair (Const x) c)

  export
  extract : Cofree c x -> x
  extract (MkCofree (MkM m)) = fst (fst m)

  export
  extend : (Cofree c a -> b) -> Cofree c a -> Cofree c b
  extend alg = MkCofree . unfoldr next . runCofree where

    next : M (Pair (Const a) c) -> Extension (Pair (Const b) c) (M (Pair (Const a) c))
    next m@(MkM layer) =
      let (_, (shp ** chld)) = fromPair {c = Const a} layer in
      let b = toConst (alg (MkCofree m)) in
      toPair (b, (shp ** \ p => chld p))
-- Eta-expanded to force Inf --^

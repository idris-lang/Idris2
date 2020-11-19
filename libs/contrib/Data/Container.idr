------------------------------------------------------------------------
-- This module is based on the following papers:

-- Categories of Containers
-- Abbott, Altenkirch, Ghani

-- Derivatives of Containers
-- Abbott, Altenkirch, Ghani, McBride
------------------------------------------------------------------------

module Data.Container

import Data.Either
import Decidable.Equality

%default total

------------------------------------------------------------------------
-- Container and their morphisms
-- * Extension is a functor from Container to Type

-- Objects of the category of containers
namespace Container

  public export
  record Container where
    constructor MkContainer
    Shape : Type
    Position : Shape -> Type

  public export
  Extension : Container -> Type -> Type
  Extension c x = (s : Shape c ** Position c s -> x)

  ||| The image of a container by @Extension@ is a functor
  public export
  Functor (Extension c) where map f (s ** p) = (s ** f . p)

-- Morphisms of the category of containers
namespace Morphism

  public export
  record Morphism (c, d : Container) where
    constructor MkMorphism
    shapeMorphism : Shape c -> Shape d
    positionMorphism : {s : Shape c} -> Position d (shapeMorphism s) -> Position c s

  public export
  Extension : Morphism c d -> Extension c x -> Extension d x
  Extension phi (s ** p) = (shapeMorphism phi s ** p . positionMorphism phi)

------------------------------------------------------------------------
-- Combinators to build containers

namespace Combinators

  -- Constant
  public export
  Const : Type -> Container
  Const k = MkContainer k (const Void)

  export
  toConst : k -> Extension (Const k) x
  toConst v = (v ** absurd)

  export
  fromConst : Extension (Const k) x -> k
  fromConst (v ** _) = v

  -- Identity
  public export
  Identity : Container
  Identity = MkContainer () (\ () => ())

  export
  toIdentity : x -> Extension Identity x
  toIdentity v = (() ** const v)

  export
  fromIdentity : Extension Identity x -> x
  fromIdentity (() ** chld) = chld ()

  -- Composition
  public export
  Compose : (d, c : Container) -> Container
  Compose d c = MkContainer (Extension d (Shape c)) (\ (shp ** chld) => (p : Position d shp ** Position c (chld p)))

  export
  toCompose : (Extension d . Extension c) x -> Extension (Compose d c) x
  toCompose (shp1 ** chld) = ((shp1 ** \ p => fst (chld p)) ** \ (p ** q) => snd (chld p) q)

  export
  fromCompose : Extension (Compose d c) x -> (Extension d . Extension c) x
  fromCompose ((shp1 ** shp2) ** chld) = (shp1 ** \ p => (shp2 p ** \ q => chld (p ** q)))

  -- Direct sum
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

  -- Pairing
  public export
  Pair : (c, d : Container) -> Container
  Pair c d = MkContainer (Shape c, Shape d) (\ (p, q) => Either (Position c p) (Position d q))

  export
  toPair : (Extension c x, Extension d x) -> Extension (Pair c d) x
  toPair ((shp1 ** chld1), (shp2 ** chld2)) = ((shp1, shp2) ** either chld1 chld2)

  export
  fromPair : Extension (Pair c d) x -> (Extension c x, Extension d x)
  fromPair ((shp1, shp2) ** chld) = ((shp1 ** chld . Left), (shp2 ** chld . Right))

  -- Branching over a Type
  public export
  Exponential : Type -> Container -> Container
  Exponential k c = MkContainer (k -> Shape c) (\ p => (v : k ** Position c (p v)))

  export
  toExponential : (k -> Extension c x) -> Extension (Exponential k c) x
  toExponential f = (fst . f ** \ (v ** p) => snd (f v) p)

  export
  fromExponential : Extension (Exponential k c) x -> (k -> Extension c x)
  fromExponential (shp ** chld) k = (shp k ** \ p => chld (k ** p))

------------------------------------------------------------------------
-- Taking various fixpoints of containers

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

  ||| @Free@ is a wrapper around @W@ to make it inference friendly.
  ||| Without this wrapper, neither @pure@ nor @bind@ are able to infer their @c@ argument.
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

  export
  join : Free c (Free c x) -> Free c x
  join = (>>= id)

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

  ||| @Cofree@ is a wrapper around @M@ to make it inference friendly.
  ||| Without this wrapper, neither @extract@ nor @extend@ are able to infer their @c@ argument.
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

  export
  duplicate : Cofree c a -> Cofree c (Cofree c a)
  duplicate = extend id

------------------------------------------------------------------------
-- Derivative

namespace Derivative

  public export
  Derivative : Container -> Container
  Derivative c = MkContainer
    (s : Shape c ** Position c s)
    (\ (s ** p) => (p' : Position c s ** Not (p === p')))

  export
  hole : (v : Extension (Derivative c) x) -> Position c (fst (fst v))
  hole ((shp ** p) ** _) = p

  export
  unplug : (v : Extension c x) -> Position c (fst v) -> (Extension (Derivative c) x, x)
  unplug (shp ** chld) p = (((shp ** p) ** chld . fst), chld p)

  export
  plug : (v : Extension (Derivative c) x) -> DecEq (Position c (fst (fst v))) => x -> Extension c x
  plug ((shp ** p) ** chld) x = (shp ** \ p' => case decEq p p' of
    Yes eq => x
    No neq => chld (p' ** neq))

  export
  toConst : Extension (Const Void) x -> Extension (Derivative (Const k)) x
  toConst v = absurd (fromConst v)

  export
  fromConst : Extension (Derivative (Const k)) x -> Extension (Const Void) x
  fromConst v = absurd (hole {c = Const _} v)

  export
  toIdentity : Extension (Derivative Identity) x
  toIdentity = ((() ** ()) ** \ (() ** eq) => absurd (eq Refl))

  export
  toSum : Extension (Sum (Derivative c) (Derivative d)) x ->
          Extension (Derivative (Sum c d)) x
  toSum v = case fromSum {c = Derivative c} {d = Derivative d} v of
    Left ((shp ** p) ** chld) => ((Left shp ** p) ** chld)
    Right ((shp ** p) ** chld) => ((Right shp ** p) ** chld)

  export
  fromSum : Extension (Derivative (Sum c d)) x ->
            Extension (Sum (Derivative c) (Derivative d)) x
  fromSum ((shp ** p) ** chld) = toSum {c = Derivative c} {d = Derivative d} $ case shp of
    Left shp => Left ((shp ** p) ** chld)
    Right shp => Right ((shp ** p) ** chld)

  export
  toPair : Extension (Sum (Pair (Derivative c) d) (Pair c (Derivative d))) x ->
           Extension (Derivative (Pair c d)) x
  toPair v = case fromSum {c = Pair (Derivative c) d} {d = Pair c (Derivative d)} v of
    Left p => let (((shp1 ** p1) ** chld1), (shp2 ** chld2)) = fromPair {c = Derivative c} p in
              (((shp1, shp2) ** Left p1) ** \ (p' ** neq) => case p' of
                  Left p1' => chld1 (p1' ** (neq . cong Left))
                  Right p2' => chld2 p2')
    Right p => let ((shp1 ** chld1), ((shp2 ** p2) ** chld2)) = fromPair {c} {d = Derivative d} p in
               (((shp1, shp2) ** Right p2) ** \ (p' ** neq) => case p' of
                  Left p1' => chld1 p1'
                  Right p2' => chld2 (p2' ** (neq . cong Right)))

  export
  fromPair : Extension (Derivative (Pair c d)) x ->
             Extension (Sum (Pair (Derivative c) d) (Pair c (Derivative d))) x
  fromPair (((shp1, shp2) ** p) ** chld) = case p of
    Left p1 => toSum {c = Pair (Derivative c) d} {d = Pair c (Derivative d)}
                     (Left (((shp1 ** p1), shp2) ** either
                         (\ p1' => chld (Left (DPair.fst p1') ** DPair.snd p1' . leftInjective))
                         (\ p2 => chld (Right p2 ** absurd))))
    Right p2 => toSum {c = Pair (Derivative c) d} {d = Pair c (Derivative d)}
                     (Right ((shp1, (shp2 ** p2)) ** either
                         (\ p1 => chld (Left p1 ** absurd))
                         (\ p2' => chld (Right (DPair.fst p2') ** DPair.snd p2' . rightInjective))))

-- TODO: compose

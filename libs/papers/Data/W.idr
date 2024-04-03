-- The content of this module is based on the paper
-- Computing with Generic Trees in Agda
-- by Stephen Dolan
-- https://dl.acm.org/doi/abs/10.1145/3546196.3550165

module Data.W

import Data.Maybe

%default total

namespace Finitary

  data Fin : Type where
    AVoid : Fin
    AUnit : (nm : String) -> Fin
    (||) : (d, e : Fin) -> Fin

  namespace Fin

    public export
    fromString : String -> Fin
    fromString = AUnit

  namespace Examples

    fbb : Fin
    fbb = "foo" || "bar" || "baz"

  record NamedUnit (nm : String) where
    constructor MkNamedUnit

  Elem : Fin -> Type
  Elem AVoid = Void
  Elem (AUnit nm) = NamedUnit nm
  Elem (d || e) = Either (Elem d) (Elem e)

  lookup : (d : Fin) -> String -> Maybe (Elem d)
  lookup AVoid s = Nothing
  lookup (AUnit nm) s = MkNamedUnit <$ guard (nm == s)
  lookup (d || e) s = Left <$> lookup d s <|> Right <$> lookup e s

  -- using a record to help the unifier
  record Shape (d : Fin) where
    constructor MkShape
    runShape : Elem d

  namespace Shape

    export
    fromString : {d : Fin} -> (nm : String) ->
                 IsJust (lookup d nm) => Shape d
    fromString {d} nm = MkShape (fromJust (lookup d nm))

  namespace Examples

    bar : Shape Examples.fbb
    bar = "bar"

  record One (nm : String) (s : Type) where
    constructor MkOne
    runOne : s

  Arr : Fin -> Type -> Type
  Arr AVoid r = ()
  Arr (AUnit nm) r = One nm r
  Arr (d || e) r = (Arr d r, Arr e r)

  export infixr 0 ~>
  record (~>) (d : Fin) (r : Type) where
    constructor MkArr
    runArr : Arr d r

  export infix 5 .=
  (.=) : (nm : String) -> s -> One nm s
  nm .= v = MkOne v

  namespace Examples

    isBar : Examples.fbb ~> Bool
    isBar = MkArr
          ( "foo" .= False
          , "bar" .= True
          , "baz" .= False
          )

  lamArr : (d : Fin) -> (Elem d -> r) -> Arr d r
  lamArr AVoid f = ()
  lamArr (AUnit nm) f = MkOne (f MkNamedUnit)
  lamArr (d || e) f = (lamArr d (f . Left), lamArr e (f . Right))

  lam : {d : Fin} -> (Elem d -> r) -> (d ~> r)
  lam {d} = MkArr . lamArr d

  appArr : (d : Fin) -> Arr d r -> (Elem d -> r)
  appArr AVoid f t = absurd t
  appArr (AUnit nm) f t = runOne f
  appArr (d || e) f (Left x) = appArr d (fst f) x
  appArr (d || e) f (Right x) = appArr e (snd f) x

  export infixl 0 $$
  ($$) : {d : Fin} -> (d ~> r) -> (Elem d -> r)
  MkArr f $$ x = appArr d f x

  beta : {d : Fin} -> (f : Elem d -> r) -> (x : Elem d) ->
         (lam {d} f $$ x) === f x
  beta = go d where

    go : (d : Fin) -> (f : Elem d -> r) -> (x : Elem d) ->
         (appArr d (lamArr d f) x) === f x
    go AVoid f x = absurd x
    go (AUnit nm) f MkNamedUnit = Refl
    go (d || e) f (Left x) = go d (f . Left) x
    go (d || e) f (Right x) = go e (f . Right) x

  eta : {d : Fin} -> (f : d ~> r) -> f === lam (\ x => f $$ x)
  eta (MkArr f) = cong MkArr (go d f) where

    go : (d : Fin) -> (f : Arr d r) ->
         f === lamArr d (\ x => appArr {r} d f x)
    go AVoid () = Refl
    go (AUnit nm) (MkOne v) = Refl
    go (d || e) (f, g) = cong2 MkPair (go d f) (go e g)

  ext : {d : Fin} -> (f, g : Elem d -> r) ->
        (eq : (x : Elem d) -> f x === g x) ->
        lam f === lam {d} g
  ext f g eq = cong MkArr (go d eq) where

    go : (d : Fin) -> {f, g : Elem d -> r} ->
         (eq : (x : Elem d) -> f x === g x) ->
         lamArr d f === lamArr d g
    go AVoid eq = Refl
    go (AUnit nm) eq = cong MkOne (eq MkNamedUnit)
    go (d || e) eq =
      cong2 MkPair (go d (\ t => eq (Left t)))
                   (go e (\ t => eq (Right t)))

  PiArr : (d : Fin) -> (b : Arr d Type) -> Type
  PiArr AVoid b = ()
  PiArr (AUnit nm) b = One nm (runOne b)
  PiArr (d || e) b = (PiArr d (fst b), PiArr e (snd b))

  record Pi (d : Fin) (b : d ~> Type) where
    constructor MkPi
    runPi : PiArr d (runArr b)

  namespace Dependent

    lamArr : (d : Fin) -> {0 b : Arr d Type} ->
             ((x : Elem d) -> appArr d b x) -> PiArr d b
    lamArr AVoid f = ()
    lamArr (AUnit nm) f = MkOne (f MkNamedUnit)
    lamArr (d || e) f =
      ( Dependent.lamArr d (\ x => f (Left x))
      , Dependent.lamArr e (\ x => f (Right x)))

    export
    lam : {d : Fin} -> {0 b : d ~> Type} ->
          ((x : Elem d) -> b $$ x) -> Pi d b
    lam {b = MkArr b} f = MkPi (Dependent.lamArr d f)

    public export
    appArr : (d : Fin) -> {0 b : Arr d Type} ->
             PiArr d b -> ((x : Elem d) -> appArr d b x)
    appArr AVoid f x = absurd x
    appArr (AUnit nm) f x = runOne f
    appArr (d || e) (f, g) (Left x) = Dependent.appArr d f x
    appArr (d || e) (f, g) (Right x) = Dependent.appArr e g x

    export
    ($$) : {d : Fin} -> {0 b : d ~> Type} ->
           Pi d b -> ((x : Elem d) -> b $$ x)
    ($$) {b = MkArr b} (MkPi f) x = Dependent.appArr d f x

    export
    beta : {d : Fin} -> {0 b : d ~> Type} ->
           (f : (x : Elem d) -> b $$ x) ->
           (x : Elem d) -> (lam {b} f $$ x) === f x
    beta {b = MkArr b} f x = go d f x where

      go : (d : Fin) -> {0 b : Arr d Type} ->
           (f : (x : Elem d) -> appArr d b x) ->
           (x : Elem d) -> appArr d {b} (lamArr d {b} f) x === f x
      go AVoid f x = absurd x
      go (AUnit nm) f MkNamedUnit = Refl
      go (d || e) f (Left x) = go d (\ x => f (Left x)) x
      go (d || e) f (Right x) = go e (\ x => f (Right x)) x

    export
    eta : {d : Fin} -> {0 b : d ~> Type} ->
          (f : Pi d b) -> lam {b} (\ x => f $$ x) === f
    eta {b = MkArr b} (MkPi f) = cong MkPi (go d f) where

      go : (d : Fin) -> {0 b : Arr d Type} ->
           (f : PiArr d b) -> (lamArr d {b} $ \ x => appArr d {b} f x) === f
      go AVoid () = Refl
      go (AUnit nm) (MkOne f) = Refl
      go (d || e) (f, g) = cong2 MkPair (go d f) (go e g)

    export
    ext : {d : Fin} -> {0 b : d ~> Type} ->
          (f, g : (x : Elem d) -> b $$ x) ->
          (eq : (x : Elem d) -> f x === g x) ->
          lam {b} f === lam g
    ext {b = MkArr b} f g eq = cong MkPi (go d eq) where

      go : (d : Fin) -> {0 b : Arr d Type} ->
           {f, g : (x : Elem d) -> appArr d b x} ->
           (eq : (x : Elem d) -> f x === g x) ->
           lamArr d {b} f === lamArr d {b} g
      go AVoid eq = Refl
      go (AUnit nm) eq = cong MkOne (eq MkNamedUnit)
      go (d || e) eq =
        cong2 MkPair (go d (\x => eq (Left x)))
                     (go e (\x => eq (Right x)))

  data W : (sh : Type) -> (pos : sh -> Fin) -> Type where
    MkW : (s : sh) -> (pos s ~> W sh pos) -> W sh pos

  mkW : (s : sh) -> Arr (pos s) (W sh pos) -> W sh pos
  mkW s f = MkW s (MkArr f)

  elim : {0 sh : Type} -> {pos : sh -> Fin} ->
         (0 pred : W sh pos -> Type) ->
         (step : (s : sh) -> (ts : pos s ~> W sh pos) ->
                 (Pi (pos s) (lam $ \ p => pred (ts $$ p))) ->
                 pred (MkW s ts)) ->
         (w : W sh pos) -> pred w
  elim pred step (MkW s (MkArr ts))
    = step s (MkArr ts) (MkPi $ ih (pos s) ts) where

    ih : (d : Fin) -> (ts : Arr d (W sh pos)) ->
         PiArr d (lamArr d $ \ p => pred (appArr d ts p))
    ih AVoid ts = ()
    ih (AUnit nm) (MkOne ts) = MkOne (elim pred step ts)
    ih (d || e) (ts, us) = (ih d ts, ih e us)

  cases : {d : Fin} -> {0 b : Shape d -> Type} ->
          PiArr d (lamArr d (b . MkShape)) -> (x : Shape d) -> b x
  cases f (MkShape x) = go (b . MkShape) f x where

    go : (0 b : Elem d -> Type) ->
         PiArr d (lamArr d b) -> (x : Elem d) -> b x
    go b f x = rewrite sym (Finitary.beta {d} b x) in Dependent.appArr d f x

  namespace Examples

    public export
    NAT : Type
    NAT = W (Shape ("zero" || "succ")) $ cases
        ( "zero" .= AVoid
        , "succ" .= "x"
        )
    zero : NAT
    zero = mkW "zero" ()

    succ : NAT -> NAT
    succ x = mkW "succ" ("x" .= x)

    NATind : (0 pred : NAT -> Type) ->
             pred Examples.zero ->
             ((n : NAT) -> pred n -> pred (succ n)) ->
             (n : NAT) -> pred n
    NATind pred pZ pS = elim pred $ cases ("zero" .= pZero, "succ" .= pSucc)

      where

        -- we're forced to do quite a bit of additional pattern matching
        -- because of a lack of eta

        pZero : (k : AVoid ~> ?) -> ? -> pred (MkW "zero" k)
        pZero (MkArr ()) ih = pZ

        pSucc : (k : "x" ~> ?) -> Pi "x" (lam (\ p => pred (k $$ p))) -> pred (MkW "succ" k)
        pSucc (MkArr (MkOne k)) (MkPi (MkOne ih)) = pS k ih

    NATindZ : {0 pred : NAT -> Type} -> {0 pZ, pS : ?} ->
              NATind pred pZ pS Examples.zero === pZ
    NATindZ = Refl

    NATindS : {0 pred : NAT -> Type} -> {0 pZ : ?} ->
              {pS : (n : NAT) -> pred n -> pred (succ n)} ->
              {0 n : NAT} -> NATind pred pZ pS (succ n) === pS n (NATind pred pZ pS n)
    NATindS = Refl

namespace PartitionedSets

  record PSet where
    constructor MkPSet
    parts : Fin
    elems : parts ~> Type

  mkPSet : (d : Fin) -> Arr d Type -> PSet
  mkPSet d e = MkPSet d (MkArr e)

  ElemArr : (parts : Fin) -> Arr parts Type -> Type
  ElemArr AVoid elt = Void
  ElemArr (AUnit nm) (MkOne e) = One nm e
  ElemArr (d || e) (f, g) = Either (ElemArr d f) (ElemArr e g)

  Elem : PSet -> Type
  Elem (MkPSet d (MkArr elt)) = ElemArr d elt

  el : {d : Fin} -> {e : d ~> Type} -> (x : Elem d) -> e $$ x -> Elem (MkPSet d e)
  el {e = MkArr e} x ex = go d e x ex where

    go : (d : Fin) -> (e : Arr d Type) -> (x : Elem d) -> appArr d e x -> ElemArr d e
    go AVoid e x ex = x
    go (AUnit nm) (MkOne e) x ex = MkOne ex
    go (d || e) (f, g) (Left x) ex = Left (go d f x ex)
    go (d || e) (f, g) (Right x) ex = Right (go e g x ex)

  Arr : (d : Fin) -> Arr d Type -> Type -> Type
  Arr AVoid e r = ()
  Arr (AUnit nm) (MkOne e) r = One nm (e -> r)
  Arr (d || e) (f , g) r = (Arr d f r, Arr e g r)

  record (~>) (p : PSet) (r : Type) where
    constructor MkArr
    runArr : Arr p.parts p.elems.runArr r

  PiArr : (d : Fin) -> (e : Arr d Type) -> Arr d e Type -> Type
  PiArr AVoid e r = ()
  PiArr (AUnit nm) (MkOne e) (MkOne r) = One nm ((x : e) -> r x)
  PiArr (d || e) (f, g) r = (PiArr d f (fst r), PiArr e g (snd r))

  record Pi (p : PSet) (r : p ~> Type) where
    constructor MkPi
    runPi : PiArr p.parts p.elems.runArr r.runArr

  lamArr : (d : Fin) -> (e : Arr d Type) ->
           (ElemArr d e -> r) -> (Arr d e r)
  lamArr AVoid f b = ()
  lamArr (AUnit nm) (MkOne f) b = MkOne (b . MkOne)
  lamArr (d || e) (f, g) b = (lamArr d f (b . Left), lamArr e g (b . Right))

  lam : {p : PSet} -> (Elem p -> r) -> (p ~> r)
  lam {p = MkPSet d (MkArr e)} f = MkArr (lamArr d e f)

  appArr : (d : Fin) -> (e : Arr d Type) ->
           (Arr d e r) -> (ElemArr d e -> r)
  appArr AVoid e b x = absurd x
  appArr (AUnit nm) (MkOne e) (MkOne b) (MkOne x) = b x
  appArr (d || e) (f, g) (b , c) (Left x) = appArr d f b x
  appArr (d || e) (f, g) (b , c) (Right x) = appArr e g c x

  ($$) : {p : PSet} -> (p ~> r) -> Elem p -> r
  ($$) {p = MkPSet d (MkArr e)} (MkArr b) = appArr d e b

  namespace Dependent

    public export
    lamArr : (d : Fin) -> (e : Arr d Type) -> (k : Arr d e Type) ->
             ((x : ElemArr d e) -> appArr d e k x) ->
             PiArr d e k
    lamArr AVoid e k b = ()
    lamArr (AUnit nm) (MkOne e) (MkOne k) b = MkOne (\ x => b (MkOne x))
    lamArr (d || e) (f, g) (k, l) b
      = ( lamArr d f k (\ x => b (Left x))
        , lamArr e g l (\ x => b (Right x)))

    public export
    lam : {p : PSet} -> {k : p ~> Type} ->
          ((x : Elem p) -> k $$ x) -> Pi p k
    lam {p = MkPSet d (MkArr e)} {k = MkArr k} b = MkPi (lamArr d e k b)

    public export
    appArr : (d : Fin) -> (e : Arr d Type) -> (k : Arr d e Type) ->
             PiArr d e k ->
             ((x : ElemArr d e) -> appArr d e k x)
    appArr AVoid e k b x = absurd x
    appArr (AUnit nm) (MkOne e) (MkOne k) (MkOne b) (MkOne x) = b x
    appArr (d || e) (f, g) (k, l) (b, c) (Left x) = appArr d f k b x
    appArr (d || e) (f, g) (k, l) (b, c) (Right x) = appArr e g l c x

    public export
    ($$) : {p : PSet} -> {k : p ~> Type} ->
           Pi p k -> ((x : Elem p) -> k $$ x)
    ($$) {p = MkPSet d (MkArr e)} {k = MkArr k} (MkPi b) = appArr d e k b

  data W : (sh : Type) -> (pos : sh -> PSet) -> Type where
    MkW : (s : sh) -> (k : pos s ~> W sh pos) -> W sh pos

  mkW : {pos : sh -> PSet} ->
        (s : sh) -> Arr ((pos s).parts) ((pos s) .elems .runArr) (W sh pos) ->
        W sh pos
  mkW s f = MkW s (MkArr f)

  elim : {0 sh : Type} -> {pos : sh -> PSet} ->
         (0 pred : W sh pos -> Type) ->
         (step : (s : sh) -> (ts : pos s ~> W sh pos) ->
                 (Pi (pos s) (lam $ \ p => pred (ts $$ p))) ->
                 pred (MkW s ts)) ->
         (w : W sh pos) -> pred w
  elim pred step (MkW s (MkArr ts)) with (step s) | (pos s)
    _ | steps | MkPSet d (MkArr e) = steps (MkArr ts) (MkPi $ ih d e ts) where

      ih : (d : Fin) -> (e : Arr d Type) -> (ts : Arr d e (W sh pos)) ->
           PiArr d e (lamArr d e $ \ p => pred (appArr d e ts p))
      ih AVoid e ts = ()
      ih (AUnit nm) (MkOne e) (MkOne ts) = MkOne (\ x => elim pred step (ts x))
      ih (d || e) (f, g) (ts, us) = (ih d f ts, ih e g us)

  namespace Examples

    -- proceed with the following assumption
    parameters { auto etaUnit : forall a. (o : () -> a) -> o === (\ _ => o ()) }

      ORD : Type
      ORD = PartitionedSets.W (Shape ("zero" || "succ" || "lim")) $ cases
          ( "zero" .= mkPSet AVoid ()
          , "succ" .= mkPSet "x" ("x" .= ())
          , "lim"  .= mkPSet "f" ("f" .= NAT)
          )

      zero : ORD
      zero = mkW "zero" ()

      succ : ORD -> ORD
      succ o = mkW "succ" ("x" .= \ _ => o)

      lim : (NAT -> ORD) -> ORD
      lim f = mkW "lim" ("f" .= f)

      ORDind : (0 pred : ORD -> Type) ->
               pred Examples.zero ->
               ((n : ORD) -> pred n -> pred (succ n)) ->
               ((f : NAT -> ORD) -> ((n : NAT) -> pred (f n)) -> pred (lim f)) ->
               (n : ORD) -> pred n
      ORDind pred pZ pS pL
        = elim pred
        $ cases ("zero" .= pZero, "succ" .= pSucc, "lim" .= pLim)

        where

          -- we're forced to do quite a bit of additional pattern matching
          -- because of a lack of eta

          pZero : (o : mkPSet AVoid () ~> ORD) -> ? -> pred (MkW "zero" o)
          pZero (MkArr ()) ih = pZ

          pSucc : (o : mkPSet (AUnit "x") ("x" .= ()) ~> ORD) ->
                  Pi (mkPSet (AUnit "x") ("x" .= ())) (lam (\p => pred (o $$ p))) ->
                  pred (MkW "succ" o)
          pSucc (MkArr (MkOne o)) (MkPi (MkOne po)) =
            rewrite etaUnit o in pS (o ()) (po ())

          pLim : (o : mkPSet (AUnit "f") ("f" .= ?A) ~> ORD) ->
                 Pi (mkPSet (AUnit "f") ("f" .= ?B)) (lam (\p => pred (o $$ p))) ->
                 pred (MkW "lim" o)
          pLim (MkArr (MkOne o)) (MkPi (MkOne po)) = pL o po


      ORDindZ : {0 pred : ORD -> Type} -> {0 pZ, pS, pL : ?} ->
                ORDind pred pZ pS pL Examples.zero === pZ
      ORDindZ = Refl

      ORDindS : {0 pred : ORD -> Type} -> {0 pZ, pL : ?} ->
                {pS : (n : ORD) -> pred n -> pred (succ n)} ->
                {0 n : ORD} -> ORDind pred pZ pS pL (succ n) === pS n (ORDind pred pZ pS pL n)
      ORDindS = Refl

      ORDindL : {0 pred : ORD -> Type} -> {0 pZ, pS : ?} ->
                {pL : (f : NAT -> ORD) -> ((n : NAT) -> pred (f n)) -> pred (lim f)} ->
                {0 f : NAT -> ORD} -> ORDind pred pZ pS pL (lim f) === pL f (\ n => ORDind pred pZ pS pL (f n))
      ORDindL = Refl

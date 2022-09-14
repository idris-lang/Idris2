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

  infixr 0 ~>
  record (~>) (d : Fin) (r : Type) where
    constructor MkArr
    runArr : Arr d r

  infix 5 .=
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

  infixl 0 $$
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

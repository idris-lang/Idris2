||| The content of this module is based on the paper
||| Auto in Agda - Programming proof search using reflection
||| by Wen Kokke and Wouter Swierstra

module Search.Auto

import Language.Reflection.TTImp
import Language.Reflection

import Data.DPair
import Data.Fin
import Data.Maybe
import Data.Nat
import Data.SnocList
import Data.String
import Data.Vect

import Syntax.PreorderReasoning

%default total

%language ElabReflection

------------------------------------------------------------------------------
-- Basics of reflection
------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- Quoting: Id term

idTerm : TTImp
idTerm = `( (\ x => x) )

idTermTest : Auto.idTerm === let x : Name; x = UN (Basic "x") in
                             ILam ? MW ExplicitArg (Just x) ? (IVar ? x)
idTermTest = Refl

------------------------------------------------------------------------------
-- Unquoting: const function

iLam : Maybe UserName -> TTImp -> TTImp -> TTImp
iLam x a sc = ILam EmptyFC MW ExplicitArg (UN <$> x) a sc

iVar : UserName -> TTImp
iVar x = IVar EmptyFC (UN x)

const : a -> b -> a
const = %runElab
      (check
      $ iLam (Just (Basic "v")) `(a)
      $ iLam Nothing            `(b)
      $ iVar (Basic "v"))

constTest : Auto.const 1 2 === 1
constTest = Refl

------------------------------------------------------------------------------
-- Section 2: Motivation
------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- Goal inspection: building tuples of default values

getPoint : Elab a
getPoint = do
  let err = fail "No clue what to do"
  Just g <- goal
    | Nothing => err
  let mval = buildValue g
  maybe err check mval

  where

    buildValue : TTImp -> Maybe TTImp
    buildValue g = do
      let qNat   : List ? = [`{Nat}, `{Prelude.Nat}, `{Prelude.Types.Nat}]
      let qBool  : List ? = [`{Bool}, `{Prelude.Bool}, `{Prelude.Basics.Bool}]
      let qList  : List ? = [`{List}, `{Prelude.List}, `{Prelude.Basics.List}]
      let qMaybe : List ? = [`{Maybe}, `{Prelude.Maybe}, `{Prelude.Types.Maybe}]
      let qPair  : List ? = [`{Pair}, `{Builtin.Pair}]
      case g of
        IVar _ n =>
          ifThenElse (n `elem` qNat)  (Just `(0)) $
          ifThenElse (n `elem` qBool) (Just `(False))
          Nothing
        IApp _ (IVar _ p) q =>
          ifThenElse (p `elem` qMaybe)
            (case buildValue q of
              Nothing => pure `(Nothing)
              Just qv => pure `(Just ~(qv)))
          $ ifThenElse (p `elem` qList)
            (case buildValue q of
              Nothing => pure `([])
              Just qv => pure `([~(qv)]))
          $ Nothing
        IApp _ (IApp _ (IVar _ p) q) r =>
          ifThenElse (not (p `elem` qPair)) Nothing $ do
            qv <- buildValue q
            rv <- buildValue r
            pure `(MkPair ~(qv) ~(rv))
        _ => Nothing

getAPoint : (List Nat, (Bool, (Maybe (List Void, Bool, Nat))), Nat)
getAPoint = %runElab getPoint

getPointTest : Auto.getAPoint === ([0], (False, Just ([], False, 0)), 0)
getPointTest = Refl

------------------------------------------------------------------------------
-- Proof automation: Even

data Even : Nat -> Type where
  EvenZ : Even Z
  EvenS : Even n -> Even (S (S n))

EvenPlus : {0 m, n : Nat} -> Even m -> Even n -> Even (m + n)
EvenPlus EvenZ      en = en
EvenPlus (EvenS em) en = EvenS (EvenPlus em en)

trivial : Even n -> Even (n + 2)
trivial en = EvenPlus en (EvenS EvenZ)

||| This is called Naïve because that's not the actual implementation, it just
||| looks like this in the paper's Motivation
namespace Naïve

  HintDB : Type
  HintDB = SnocList Name

  hints : HintDB
  hints = [< `{EvenZ}, `{EvenS}, `{EvenPlus}]

------------------------------------------------------------------------------
-- Section 3: Proof search
------------------------------------------------------------------------------

namespace RuleName

  public export
  data RuleName : Type where
    Free  : Name -> RuleName
    Bound : Nat -> RuleName

  export
  toName : RuleName -> Name
  toName (Free nm) = nm
  toName (Bound n) = DN (pack $ display n)
                   $ MN "bound_variable_auto_search" (cast n)

    where
    display : Nat -> List Char
    display n =
      let (p, q) = divmodNatNZ n 26 ItIsSucc in
      cast (q + cast 'a') :: if p == 0 then [] else display (assert_smaller n (pred p))


export
Show RuleName where
  show (Free nm) = "Free \{show nm}"
  show (Bound n) = "Bound \{show n}"
  -- show . toName

namespace TermName

  public export
  data TermName : Type where
    UName : Name -> TermName
    Bound : Nat -> TermName
    Arrow : TermName

export
Eq TermName where
  UName n1 == UName n2 = n1 == n2
  Bound n1 == Bound n2 = n1 == n2
  Arrow == Arrow = True
  _ == _ = False

||| Proof search terms
public export
data Tm : Nat -> Type where
  Var : Fin n -> Tm n
  Con : TermName -> List (Tm n) -> Tm n

export
showTerm : (ns : SnocList Name) -> Tm (length ns) -> String
showTerm ns = go Open where

  goVar : (ns : SnocList Name) -> Fin (length ns) -> String
  goVar (_ :< n) FZ = show n
  goVar (ns :< _) (FS k) = goVar ns k

  go : Prec -> Tm (length ns) -> String
  go d (Var k) = goVar ns k
  go d (Con (UName n) []) = show n -- (dropNS n)
  go d (Con Arrow [a,b])
    = showParens (d > Open) $
        unwords [ go App a, "->", go Open b ]
  go d (Con (UName n) [a,b])
    = showParens (d > Open) $
        -- let n = dropNS n in
        if isOp n then unwords [ go App a, show n, go Open b ]
        else unwords [ show n, go App a, go App b ]
  go d (Con (UName n) ts)
    = showParens (d > Open) $
        unwords (show n :: assert_total (map (go App) ts))
  go _ _ = ""

public export
Env : (Nat -> Type) -> Nat -> Nat -> Type
Env t m n = Fin m -> t n

export
rename : Env Fin m n -> Tm m -> Tm n
rename rho (Var x) = Var (rho x)
rename rho (Con f xs) = Con f (assert_total $ map (rename rho) xs)

export
subst : Env Tm m n -> Tm m -> Tm n
subst rho (Var x) = rho x
subst rho (Con f xs) = Con f (assert_total $ map (subst rho) xs)

export
split : Tm m -> (List (Tm m), Tm m)
split = go [<] where

  go : SnocList (Tm m) -> Tm m -> (List (Tm m), Tm m)
  go acc (Con Arrow [a,b]) = go (acc :< a) b
  go acc t = (acc <>> [], t)

------------------------------------------------------------------------------
-- Interlude: First-order unification by structural recursion by Conor McBride
------------------------------------------------------------------------------

export
thin : Fin (S n) -> Fin n -> Fin (S n)
thin FZ y = FS y
thin (FS x) FZ = FZ
thin (FS x) (FS y) = FS (thin x y)

export
thinInjective : (x : Fin (S n)) -> (y, z : Fin n) -> thin x y === thin x z -> y === z
thinInjective FZ y z eq = injective eq
thinInjective (FS x) FZ FZ eq = Refl
thinInjective (FS x) (FS y) (FS z) eq = cong FS (thinInjective x y z $ injective eq)

export
{x : Fin (S n)} -> Injective (thin x) where
  injective = thinInjective x ? ?

export
thinnedApart : (x : Fin (S n)) -> (y : Fin n) -> Not (thin x y === x)
thinnedApart FZ y = absurd
thinnedApart (FS x) FZ = absurd
thinnedApart (FS x) (FS y) = thinnedApart x y . injective

export
thinApart : (x, y : Fin (S n)) -> Not (x === y) -> (y' ** thin x y' === y)
thinApart FZ FZ neq = absurd (neq Refl)
thinApart FZ (FS y') neq = (y' ** Refl)
thinApart (FS FZ) FZ neq = (FZ ** Refl)
thinApart (FS (FS x)) FZ neq = (FZ ** Refl)
thinApart (FS x@FZ) (FS y) neq = bimap FS (\prf => cong FS prf) (thinApart x y (\prf => neq $ cong FS prf))
thinApart (FS x@(FS{})) (FS y) neq = bimap FS (\prf => cong FS prf) (thinApart x y (\prf => neq $ cong FS prf))

public export
data Thicken : (x, y : Fin n) -> Type where
  EQ  : Thicken x x
  NEQ : (y : Fin n) -> Thicken x (thin x y)

export
thicken : (x, y : Fin n) -> Thicken x y
thicken FZ FZ = EQ
thicken FZ (FS y) = NEQ y
thicken (FS FZ) FZ = NEQ FZ
thicken (FS (FS{})) FZ = NEQ FZ
thicken (FS x) (FS y) with (thicken x y)
  thicken (FS x) (FS x) | EQ = EQ
  thicken (FS x) (FS (thin x y)) | NEQ y = NEQ (FS y)

export
check : Fin (S n) -> Tm (S n) -> Maybe (Tm n)
check x (Var y) = case thicken x y of
  EQ => Nothing
  NEQ y' => Just (Var y')
check x (Con f ts) = Con f <$> assert_total (traverse (check x) ts)


export
for : Tm n -> Fin (S n) -> Env Tm (S n) n
(t `for` x) y = case thicken x y of
  EQ => t
  NEQ y' => Var y'

public export
data AList : (m, n : Nat) -> Type where
  Lin : AList m m
  (:<) : AList m n -> (Fin (S m), Tm m) -> AList (S m) n

export
(++) : AList m n -> AList l m -> AList l n
xts ++ [<] = xts
xts ++ (yus :< yt) = (xts ++ yus) :< yt

export
toSubst : AList m n -> Env Tm m n
toSubst [<] = Var
toSubst (xts :< (x , t)) =  subst (toSubst xts) . (t `Auto.for` x)

record Unifying m where
  constructor MkUnifying
  {target : Nat}
  rho : AList m target
  -- TODO: add proofs too?

flexFlex : {m : _} -> (x, y : Fin m) -> Unifying m
flexFlex x y = case thicken x y of
  EQ => MkUnifying [<]
  NEQ y' => MkUnifying [<(x, Var y')]

flexRigid : {m : _} -> (x : Fin m) -> (t : Tm m) -> Maybe (Unifying m)
-- We only have two cases so that Idris can see that `m` ought to be S-headed
flexRigid x@FZ t = do
  t' <- check x t
  Just (MkUnifying [<(x,t')])
flexRigid x@(FS{}) t = do
  t' <- check x t
  Just (MkUnifying [<(x,t')])

export
mgu : {m : _} -> (s, t : Tm m) -> Maybe (Unifying m)

amgu : {n : _} -> (s, t : Tm m) -> AList m n -> Maybe (Unifying m)
amgus : {n : _} -> (s, t : List (Tm m)) -> AList m n -> Maybe (Unifying m)

mgu s t = amgu s t [<]

amgu (Con f ts) (Con g us) acc
  = do guard (f == g)
       amgus ts us acc
amgu (Var x) (Var y) [<] = Just (flexFlex x y)
amgu (Var x) t [<] = flexRigid x t
amgu s (Var y) [<] = flexRigid y s
amgu s t (rho :< (x, v)) = do
  let sig = v `for` x
  MkUnifying acc <- amgu (subst sig s) (subst sig t) rho
  Just (MkUnifying (acc :< (x, v)))

amgus [] [] acc = Just (MkUnifying acc)
amgus (t :: ts) (u :: us) acc = do
  MkUnifying acc <- amgu t u acc
  amgus ts us acc
amgus _ _ _ = Nothing

------------------------------------------------------------------------------
-- End of the interlude
------------------------------------------------------------------------------

export
record Rule where
  constructor MkRule
  context : SnocList Name
  ruleName : RuleName
  {arity : Nat}
  premises : Vect arity (Tm (length context))
  conclusion : Tm (length context)

export
(.scope) : Rule -> Nat
r .scope = length r.context

export
Show Rule where
  show (MkRule context nm premises conclusion)
       = unlines
       $ ifThenElse (null context) "" ("  forall \{unwords (map show context <>> [])}.")
      :: map (("  " ++) . showTerm context) (toList premises)
    ++ [ replicate 25 '-' ++ " " ++ show nm
       , "  " ++ showTerm context conclusion
       ]

public export
HintDB : Type
HintDB = List Rule

namespace Example

  data Add : (m, n, p : Nat) -> Type where
    AddBase : Add 0 n n
    AddStep : Add m n p -> Add (S m) n (S p)

  add : Vect 3 (Tm m) -> Tm m
  add = Con (UName `{Search.Auto.Example.Add}) . toList

  zro : Tm m
  zro = Con (UName `{Prelude.Types.Z}) []

  suc : Vect 1 (Tm m) -> Tm m
  suc = Con (UName `{Prelude.Types.S}) . toList

  qAddBase : Rule
  qAddBase
    = MkRule [< UN (Basic "n")] (Free `{AddBase})
      []
    -------------------------------
    $ add [ zro, Var FZ, Var FZ ]

  qAddStep : Rule
  qAddStep
    = MkRule (UN . Basic <$> [<"m","n","p"]) (Free `{AddStep})
      [add [Var 2, Var 1, Var 0]]
    -----------------------------
    $ add [suc [Var 2], Var 1, suc [Var 0]]

  addHints : HintDB
  addHints = [qAddBase, qAddStep]


||| A search Space represents the space of possible solutions to a problem.
||| It is a finitely branching, potentially infinitely deep, tree.
||| E.g. we can prove `Nat` using:
||| 1. either Z or S                  (finitely branching)
||| 2. arbitrarily many S constructor (unbounded depth)
public export
data Space : Type -> Type where
  Solution   : a -> Space a
  Candidates : List (Inf (Space a)) -> Space a

||| A proof is a completed tree where each node is the invocation of a rule
||| together with proofs for its premises, or a lambda abstraction with a
||| subproof.
public export
data Proof : Type where
  Call : RuleName -> List Proof -> Proof
  Lam : Nat -> Proof -> Proof

export
Show Proof where
  show prf = unlines (go "" [<] prf <>> []) where
    go : (indent : String) -> SnocList String -> Proof -> SnocList String
    go indent acc (Call r prfs) =
      let acc = acc :< (indent ++ show r) in
      assert_total $ foldl (go (" " ++ indent)) acc prfs
    go indent acc (Lam n prf) =
      let acc = acc :< (indent ++ "\\ x" ++ show n) in
      assert_total $ go (" " ++ indent) acc prf


||| A partial proof is a vector of goals and a continuation which, provided
||| a proof for each of the goals, returns a completed proof
public export
record PartialProof (m : Nat) where
  constructor MkPartialProof
  leftovers : Nat
  goals : Vect leftovers (Tm m)
  continuation : Vect leftovers Proof -> Proof

||| Helper function to manufacture a proof step
export
apply : (r : Rule) -> Vect (r.arity + k) Proof -> Vect (S k) Proof
apply r args = let (premises, rest) = splitAt r.arity args in
               Call r.ruleName (toList premises) :: rest

mkVars : (m : Nat) -> (vars : SnocList Name ** length vars = m)
mkVars Z = ([<] ** Refl)
mkVars m@(S m') = bimap (:< UN (Basic $ "_invalidName" ++ show m)) (\prf => cong S prf) (mkVars m')

solveAcc : {m : _} -> Nat -> HintDB -> PartialProof m -> Space Proof
solveAcc idx rules (MkPartialProof 0     goals k)
  = Solution (k [])
solveAcc idx rules (MkPartialProof (S ar) (Con Arrow [a, b] :: goals) k)
  -- to discharge an arrow type, we:
  -- 1. Bind a new variable
  -- 2. Add a new rule corresponding to that variable whose type is based on the function's domain
  -- 3. Try to build an element of the codomain
  = let (prems, res) = split a in
    let (vars ** Refl) = mkVars m in
    let rule = MkRule vars (Bound idx) (fromList prems) res in
    Candidates [ solveAcc (S idx) (rule :: rules)
               $ MkPartialProof (S ar) (b :: goals)
               $ \ (b :: prfs) => k (Lam idx b :: prfs)]
solveAcc idx rules (MkPartialProof (S ar) (g :: goals) k)
  = Candidates (assert_total $ map step rules) where

  step : Rule -> Inf (Space Proof)
  step r with (mgu (rename (weakenN r.scope) g) (rename (shift m) (conclusion r)))
    _ | Nothing = Candidates []
    _ | Just sol = let sig = toSubst sol.rho in
                   solveAcc idx rules $ MkPartialProof
                     (r.arity + ar)
                     (map (subst (sig . shift m)) r.premises
                      ++ map (subst (sig . weakenN r.scope)) goals)
                     (k . apply r)

||| Solve takes a database of hints, a goal to prove and returns
||| the full search space.
export
solve : {m : _} -> Nat -> HintDB -> Tm m -> Space Proof
solve idx rules goal = solveAcc idx rules (MkPartialProof 1 [goal] head)

||| Depth first search strategy to explore a search space.
||| This is made total by preemptively limiting the depth the search
||| is willing to explore.
export
dfs : (depth : Nat) -> Space a -> List a
dfs _ (Solution x) = [x]
dfs 0 _ = []
dfs (S k) (Candidates cs) = cs >>= \ c => dfs k c

namespace Example

  four : Maybe Proof
  four = head'
       $ dfs 5
       $ solve {m = 0} 0 addHints
       $ add [ suc [suc [zro]]
             , suc [suc [zro]]
             , suc [suc [suc [suc [zro]]]]
             ]

lengthDistributesOverFish : (sx : SnocList a) -> (xs : List a) ->
                            length (sx <>< xs) === length sx + length xs
lengthDistributesOverFish sx [] = sym $ plusZeroRightNeutral ?
lengthDistributesOverFish sx (x :: xs) = Calc $
  |~ length ((sx :< x) <>< xs)
  ~~ length (sx :< x) + length xs ...( lengthDistributesOverFish (sx :< x) xs)
  ~~ S (length sx) + length xs    ...( Refl )
  ~~ length sx + S (length xs)    ...( plusSuccRightSucc ? ? )
  ~~ length sx + length (x :: xs) ...( Refl )

convertVar : (vars : SnocList Name) -> Name -> Tm (length vars)
convertVar [<] nm = Con (UName nm) []
convertVar (sx :< x) nm = if x == nm then Var FZ else go sx [x] FZ

  where

  go : (vars : SnocList Name) -> (ctxt : List Name) ->
       Fin (length ctxt) -> Tm (length (vars <>< ctxt))
  go [<] ctxt k = Con (UName nm) []
  go (sx :< x) ctxt k =
    if x == nm
    then Var $ rewrite lengthDistributesOverFish sx (x :: ctxt) in
               rewrite plusCommutative (length sx) (S (length ctxt)) in
               weakenN (length sx) (FS k)
    else go sx (x :: ctxt) (FS k)

skolemVar : SnocList Name -> Name -> Tm 0
skolemVar [<] nm = Con (UName nm) []
skolemVar (sx :< x) nm
  = if nm == x then Con (Bound (length sx)) [] else skolemVar sx nm

getFnArgs : TTImp -> (TTImp, List TTImp)
getFnArgs = go [] where

  go : List TTImp -> TTImp -> (TTImp, List TTImp)
  go acc (IApp _ f t) = go (t :: acc) f
  go acc (INamedApp _ f n t) = go acc f
  go acc (IAutoApp _ f t) = go acc f
  go acc t = (t, acc)

parameters (0 f : SnocList Name -> Nat) (cvar : (vars : SnocList Name) -> Name -> Tm (f vars))

  ||| Converts a type of the form (a -> (a -> b -> c) -> b -> c)
  ||| to our internal representation
  export
  convert : (vars : SnocList Name) -> TTImp -> Either TTImp (Tm (f vars))
  convert vars (IVar _ nm) = pure (cvar vars nm)
  convert vars t@(IApp x y z) = do
    let (IVar _ nm, args) = getFnArgs t
      | _ => Left t
    let (Con nm []) = convertVar vars nm
      | _ => Left t
    Con nm <$>  assert_total (traverse (convert vars) args)
  convert vars t@(IPi _ _ ExplicitArg (Just n@(UN{})) argTy retTy) = Left t
  convert vars (IPi _ _ ExplicitArg _ argTy retTy)
    = do a <- convert vars argTy
         b <- convert vars retTy
         pure (Con Arrow [a,b])
  convert vars t = Left t

  ||| Parse a type of the form
  ||| forall a b c. a -> (a -> b -> c) -> b -> c to
  ||| 1. a scope [<a,b,c]
  ||| 2. a representation of the rest
  export
  parseType : TTImp -> Either TTImp (vars : SnocList Name ** Tm (f vars))
  parseType = go [<] where

    go : SnocList Name -> TTImp -> Either TTImp (vars : SnocList Name ** Tm (f vars))
    go vars (IPi _ _ ImplicitArg mn _ retTy)
      = go (vars :< fromMaybe (UN Underscore) mn) retTy
    go vars t = map (MkDPair vars) (convert vars t)

||| Parse a type, where bound variables are flexible variables
export
parseRule : TTImp -> Either TTImp (vars : SnocList Name ** Tm (length vars))
parseRule = parseType length convertVar

||| Parse a type, where bound variables are rigid variables
export
parseGoal : TTImp -> Either TTImp (SnocList Name, Tm 0)
parseGoal t = do
  (vars ** g) <- parseType (\ _ => 0) skolemVar t
  pure (vars, g)

export
mkRule : Name -> Elab Rule
mkRule nm = do
  [(_, ty)] <- getType nm
    | [] => fail "Couldn't find \{show nm}."
    | nms => fail $ concat
                  $ "Ambiguous name \{show nm}, could be any of: "
                  :: intersperse ", " (map (show . fst) nms)
  logMsg (show nm) 1 "Found the definition."
  let Right (m ** tm) = parseRule ty
    | Left t => fail "The type of \{show nm} is unsupported, chocked on \{show t}"
  logMsg (show nm) 1 "Parsed the type."
  let (premises, goal) = split tm
  logMsg (show nm) 1 "Successfully split the type."
  let r = MkRule m (Free nm) (fromList premises) goal
  logMsg "auto.quoting.\{show nm}" 1 ("\n" ++ show r)
  pure r

namespace Example

  evenHints : HintDB
  evenHints = with [Prelude.(::), Prelude.Nil]
            [ %runElab (mkRule `{EvenZ})
            , %runElab (mkRule `{EvenS})
            , %runElab (mkRule `{EvenPlus})
            ]

export
getGoal : Elab (HintDB, Tm 0)
getGoal = do
  Just gty <- goal
    | Nothing => fail "No goal to get"
  let Right (vars, qgty) = parseGoal gty
    | Left t => fail "Couldn't parse goal type: \{show t}"
  let (qass, qg) = split qgty
  pure (toPremises (length vars) qass, qg)

  where
  toPremises : Nat -> List (Tm 0) -> HintDB
  toPremises acc [] = []
  toPremises acc (t :: ts)
    = let (prems, res) = split t in
      MkRule [<] (Bound acc) (fromList prems) res :: toPremises (S acc) ts

export
unquote : Proof -> TTImp
unquote (Call f xs)
  = foldl (IApp emptyFC) (IVar emptyFC (toName f))
  $ assert_total (map unquote xs)
unquote (Lam n prf)
  = ILam emptyFC MW ExplicitArg (Just $ toName (Bound n)) (Implicit emptyFC False)
  $ unquote prf

export
intros : List a -> TTImp -> TTImp
intros = go 0 where

  go : Nat -> List a -> TTImp -> TTImp
  go idx [] t = t
  go idx (_ :: as) t
    = ILam emptyFC MW ExplicitArg (Just $ toName (Bound idx)) (Implicit emptyFC False)
    $ go (S idx) as t

export
bySearch : (depth : Nat) -> HintDB -> Elab a
bySearch depth rules = do
  (rules', g) <- getGoal
  logMsg "auto.search.goal" 1 (showTerm [<] g)
  let rules = rules ++ rules'
  logMsg "auto.search.rules" 1 (unlines $ map show rules')
  let (prf :: _) = dfs depth (solve (length rules') rules g)
    | _ => fail "Couldn't find proof for goal"
  check (intros rules' (unquote prf))

namespace Example

  idTest : a -> a
  idTest = %runElab (bySearch 2 [])

  constTest : a -> b -> a
  constTest = %runElab (bySearch 2 [])

  sTest : (a -> b -> c) -> (a -> b) -> a -> c
  sTest = %runElab (bySearch 4 [])

  -- The type of `MkPair` is falsely dependent and makes the machinery choke
  -- so we define this one instead
  mkPair : a -> b -> Pair a b
  mkPair a b = (a, b)

  listFromDupTest : (a -> (a -> (a, a)) -> List a) -> a -> List a
  listFromDupTest = %runElab (bySearch 6 [%runElab (mkRule `{mkPair})])

  even0Test : Even Z
  even0Test = %runElab (bySearch 1 evenHints)

  even2Test : Even 2
  even2Test = %runElab (bySearch 2 evenHints)

  evenPlusTest : Even n -> Even m -> Even (m + n)
  evenPlusTest = %runElab (bySearch 3 evenHints)

  evenPlus2Test : Even m -> Even (m + 2)
  evenPlus2Test = %runElab (bySearch 4 evenHints)

  addBaseTest : Add Z Z Z
  addBaseTest = %runElab (bySearch 3 addHints)

  add2TwiceTest : Add 2 2 4
  add2TwiceTest = %runElab (bySearch 3 addHints)

||| The content of this module is based on the MSc Thesis
||| Coinductive Formalization of SECD Machine in Agda
||| by Adam Krupička

module Language.IntrinsicTyping.SECD

import public Data.Late
import Data.List.Elem
import public Data.List.Quantifiers

%default total

------------------------------------------------------------------------
-- Machine types

public export
data Ty
  = TyInt
  | TyBool
  | TyPair Ty Ty
  | TyList Ty
  | TyFun Ty Ty

%name Ty a,b

public export
data Const : Ty -> Type where
  AnInt : Int -> Const TyInt
  True  : Const TyBool
  False : Const TyBool

public export
fromInteger : Integer -> Const TyInt
fromInteger n = AnInt (cast n)

------------------------------------------------------------------------
-- Machine states

public export
Stack : Type
Stack = List Ty

public export
Env : Type
Env = List Ty

public export
FunDump : Type
FunDump = List (Ty, Ty)

public export
record State where
  constructor MkState
  stack : Stack
  env   : Env
  dump  : FunDump

------------------------------------------------------------------------
-- Instructions as state-transforming operations

data Step  : State -> State -> Type
data Steps : State -> State -> Type

public export
data Step  : State -> State -> Type where
  -- Loading

  ||| Load a constant of a base type
  LDC : (c : Const ty) -> MkState s e f `Step` MkState (ty :: s) e f
  ||| Load a value from an address in the environment
  LDA : Elem ty e ->
        MkState s e f `Step` MkState (ty :: s) e f
  ||| Load a recursive function
  LDF : (MkState [] (a :: e) ((a, b) :: f) `Steps` MkState [b] (a :: e) ((a, b) :: f)) ->
        MkState s e f `Step` MkState (TyFun a b :: s) e f
  ||| Load a function for recursive application
  LDR : Elem (a,b) f ->
        MkState s e f `Step` MkState (TyFun a b :: s) e f

  -- Applying & returning

  ||| Apply a function to its argument
  APP : MkState (a :: TyFun a b :: s) e f `Step` MkState (b :: s) e f
  ||| Apply a function to its argument, tail call
  TAP : MkState (a :: TyFun a b :: s) e f `Step` MkState (b :: s) e f
  ||| Return a value from inside a function
  RTN : MkState (b :: s) e ((a, b) :: f) `Step` MkState [ b ] e ((a, b) :: f)

  -- If destructor

  ||| Branch over a boolean
  BCH : (l, r : MkState s e f `Steps` MkState s' e f) ->
        MkState (TyBool :: s) e f `Step` MkState s' e f

  -- Stack manipulation

  ||| Flip the stack's top values
  FLP : MkState (a :: b :: s) e f `Step` MkState (b :: a :: s) e f

  -- List primitives

  ||| Nil constructor
  NIL : MkState s e f `Step` MkState (TyList a :: s) e f
  ||| Cons constructor
  CNS : MkState (a :: TyList a :: s) e f `Step` MkState (TyList a :: s) e f
  ||| Head destructor
  HED : MkState (TyList a :: s) e f `Step` MkState (a :: s) e f
  ||| Tail destructor
  TAL : MkState (TyList a :: s) e f `Step` MkState (TyList a :: s) e f

  -- Pair primitives

  ||| Pair constructor
  MKP : MkState (a :: b :: s) e f `Step` MkState (TyPair a b :: s) e f
  ||| First pair destructor
  FST : MkState (TyPair a b :: s) e f `Step` MkState (a :: s) e f
  ||| Second pair destructor
  SND : MkState (TyPair a b :: s) e f `Step` MkState (b :: s) e f

  -- Int primitives

  ||| Addition of ints
  ADD : MkState (TyInt :: TyInt :: s) e f `Step` MkState (TyInt :: s) e f
  ||| Subtraction of ints
  SUB : MkState (TyInt :: TyInt :: s) e f `Step` MkState (TyInt :: s) e f
  ||| Multiplication of ints
  MUL : MkState (TyInt :: TyInt :: s) e f `Step` MkState (TyInt :: s) e f

  -- Bool primitives

  ||| Structural equality test
  EQB : {a : Ty} -> MkState (a :: a :: s) e f `Step` MkState (TyBool :: s) e f
  ||| Boolean negation
  NOT : MkState (TyBool :: s) e f `Step` MkState (TyBool :: s) e f


------------------------------------------------------------------------
-- Reflexive transitive closures & combinators

public export
data Steps : State -> State -> Type where
  Nil  : Steps s s
  (::) : Step s t -> Steps t u -> Steps s u

public export
data Stepz : State -> State -> Type where
  Lin  : Stepz s s
  (:<) : Stepz s t -> Step t u -> Stepz s u

public export
(<>>) : Stepz s t -> Steps t u -> Steps s u
[<] <>> ts = ts
(ss :< s) <>> ts = ss <>> (s :: ts)

public export
(<><) : Stepz s t -> Steps t u -> Stepz s u
ss <>< [] = ss
ss <>< (t :: ts) = (ss :< t) <>< ts

public export
(++) : Steps s t -> Steps t u -> Steps s u
[] ++ ts = ts
(s :: ss) ++ ts = s :: (ss ++ ts)

------------------------------------------------------------------------
-- Basic operations & examples

public export
NUL : {a : Ty} -> MkState (TyList a :: s) e f `Steps` MkState (TyBool :: s) e f
NUL = [NIL, EQB]

public export
LDL : List Int -> MkState s e f `Steps` MkState (TyList TyInt :: s) e f
LDL vs = go [<NIL] ([<] <>< vs) <>> [] where

  go : MkState s e f `Stepz` MkState (TyList TyInt :: s) e f ->
       SnocList Int ->
       MkState s e f `Stepz` MkState (TyList TyInt :: s) e f
  go acc [<] = acc
  go acc (vs :< v) = go (acc :< LDC (AnInt v) :< CNS) vs

FVE : MkState [] [] [] `Steps` MkState [TyInt] [] []
FVE = [LDC 2, LDC 3, ADD]

INC : MkState [] (TyInt :: e) ((TyInt, TyInt) :: f)
     `Steps` MkState [TyInt] (TyInt :: e) ((TyInt, TyInt) :: f)
INC =
  [ LDA Here
  , LDC 1
  , ADD
  ]

INC2 : MkState [] [] [] `Steps` MkState [TyInt] [] []
INC2 =
  [ LDF INC
  , LDC 2
  , APP
  ]

THR : MkState [] [] [] `Steps` MkState [TyInt] [] []
THR =
  [ LDF [ LDF [LDA Here, LDA (There Here), ADD, RTN ], RTN ]
  , LDC 1
  , APP
  , LDC 2
  , APP
  ]

public export
PLS : MkState s e f `Step` MkState (TyFun TyInt (TyFun TyInt TyInt) :: s) e f
PLS = LDF [ LDF [ LDA Here
                , LDA (There Here)
                , ADD
                , RTN
                ]]

public export
MAP : {a : Ty} -> MkState [] e f `Step` MkState [ TyFun (TyFun a b) (TyFun (TyList a) (TyList b )) ] e f
MAP = LDF [LDF ( LDA Here
              :: NUL
              ++ [ BCH [ NIL ]
                       [ LDR Here, LDA Here, TAL, APP
                       , LDA (There Here), LDA Here, HED, APP
                       , CNS
                       ]
                 ]
              )]

public export
FLD : {a : Ty} -> MkState [] e f `Step`
      MkState [TyFun (TyFun b (TyFun a b)) (TyFun b (TyFun (TyList a) b))] e f
FLD = LDF [ LDF [ LDF ( LDA Here
                     :: NUL
                     ++ [ BCH [ LDA (There Here) ]
                              [ LDA (There (There Here)) -- c
                              , LDA (There Here) -- n
                              , APP -- c n
                              , LDA Here -- x :: xs
                              , HED
                              , APP -- c n x
                              , LDR (There Here) -- foldl c
                              , FLP
                              , APP -- foldl c (c n x)
                              , LDA Here -- x :: xs
                              , TAL -- xs
                              , APP -- fold c (c n x) xs
                              ]
                        ])]]

public export
SUM : MkState [] e f `Steps`
      MkState [TyFun (TyList TyInt) TyInt] e f
SUM = [ FLD
      , PLS
      , APP
      , LDC 0
      , APP
      ]


------------------------------------------------------------------------
-- Meaning

data Closure : (a, b : Ty) -> Type

namespace Ty

  public export
  Meaning : Ty -> Type
  Meaning TyInt = Int
  Meaning TyBool = Bool
  Meaning (TyPair a b) = (Meaning a, Meaning b)
  Meaning (TyList a) = List (Meaning a)
  Meaning (TyFun a b) = Closure a b

  public export
  fromConst : Const ty -> Meaning ty
  fromConst (AnInt i) = i
  fromConst True = True
  fromConst False = False

namespace StackOrEnv

  public export
  Meaning : List Ty -> Type
  Meaning = All Meaning

namespace FunDump

  public export
  0 Meaning : FunDump -> Type
  Meaning [] = ()
  Meaning ((a, b) :: f) = (Closure a b, Meaning f)

  public export
  tail : {0 f : FunDump} -> Meaning (ab :: f) -> Meaning f
  tail {ab = (a, b)} (_, f) = f

  public export
  lookup : Meaning f -> Elem (a,b) f -> Closure a b
  lookup (cl, _) Here = cl
  lookup {f = (a, b) :: _} (_, f) (There p) = lookup f p

namespace State

  public export
  record Meaning (st : State) where
    constructor MkMeaning
    stackVal : Meaning st.stack
    envVal   : Meaning st.env
    dumpVal  : Meaning st.dump

public export
record Closure (a, b : Ty) where
  constructor MkClosure
  {0 localEnv : Env}
  {0 localFunDump : FunDump}
  code : MkState [] (a :: localEnv) ((a, b) :: localFunDump)
         `Steps` MkState [b] (a :: localEnv) ((a, b) :: localFunDump)
  envVal : Meaning localEnv
  dumpVal : Meaning localFunDump

public export
eqb : (ty : Ty) -> (l, r : Meaning ty) -> Bool
public export
eqbs : (ty : Ty) -> (l, r : Meaning (TyList ty)) -> Bool

eqb TyInt l r = l == r
eqb TyBool l r = l == r
eqb (TyPair a b) (l1, l2) (r1, r2) = eqb a l1 r1 && eqb b l2 r2
eqb (TyList a) l r = eqbs a l r
eqb (TyFun a b) l r = False

eqbs a [] [] = True
eqbs a (l :: ls) (r :: rs) = eqb a l r && eqbs a ls rs
eqbs a _ _ = False

-- TODO: these are not actually tail recursive.
-- APP is the biggest culprit

public export
steps : Meaning st -> Steps st st' -> Late (Meaning st')
public export
step : Meaning st -> Step st st' -> Late (Meaning st')

steps st [] = Now st
steps st (stp :: stps)
  = do st' <- step st stp
       steps st' stps

step (MkMeaning s e f) (LDC c) = Now (MkMeaning (fromConst c :: s) e f)
step (MkMeaning s e f) (LDA p) = Now (MkMeaning (indexAll p e :: s) e f)
step (MkMeaning s e f) (LDF cd) = Now (MkMeaning (MkClosure cd e f :: s) e f)
step (MkMeaning s e f) (LDR p) = Now (MkMeaning (lookup f p :: s) e f)

step (MkMeaning (a :: fun :: s) e f) APP
  -- TODO: Nisse-style transform for guardedness
  = Later $ do let MkClosure cd e1 f1 = fun
               MkMeaning [v] _ _ <- assert_total (steps (MkMeaning [] (a :: e1) (fun, f1)) cd)
               Now (MkMeaning (v :: s) e f)
step (MkMeaning (a :: fun :: s) e f) TAP
  -- TODO: Actual tail calls
  = Later $ do let MkClosure cd e1 f1 = fun
               MkMeaning [v] _ _ <- assert_total (steps (MkMeaning [] (a :: e1) (fun, f1)) cd)
               Now (MkMeaning (v :: s) e f)
step (MkMeaning (v :: s) e f) RTN = Now (MkMeaning [v] e f)

step (MkMeaning (b :: s) e f) (BCH l r)
  = let st = MkMeaning s e f in
    ifThenElse b
      (Later (steps st l))
      (Later (steps st r))

step (MkMeaning (a :: b :: s) e f) FLP = Now (MkMeaning (b :: (a :: s)) e f)

step (MkMeaning s e f) NIL = Now (MkMeaning ([] :: s) e f)
step (MkMeaning (x :: xs :: s) e f) CNS = Now (MkMeaning ((x :: xs) :: s) e f)
step (MkMeaning (xs :: s) e f) HED = case xs of
  [] => never
  (x :: _) => Now (MkMeaning (x :: s) e f)
step (MkMeaning (xs :: s) e f) TAL = case xs of
  [] => never
  (_ :: xs) => Now (MkMeaning (xs :: s) e f)

step (MkMeaning (a :: b :: s) e f) MKP = Now (MkMeaning ((a, b) :: s) e f)
step (MkMeaning (ab :: s) e f) FST = Now (MkMeaning (fst ab :: s) e f)
step (MkMeaning (ab :: s) e f) SND = Now (MkMeaning (snd ab :: s) e f)

step (MkMeaning (m :: n :: s) e f) ADD = Now (MkMeaning (m + n :: s) e f)
step (MkMeaning (m :: n :: s) e f) SUB = Now (MkMeaning (m - n :: s) e f)
step (MkMeaning (m :: n :: s) e f) MUL = Now (MkMeaning (m * n :: s) e f)

step (MkMeaning (x :: y :: s) e f) EQB = Now (MkMeaning (eqb _ x y :: s) e f)
step (MkMeaning (b :: s) e f) NOT = Now (MkMeaning (not b :: s) e f)

public export
run : MkState [] [] [] `Steps` MkState (ty :: _) [] [] -> Nat -> Maybe (Meaning ty)
run cd n
  = do MkMeaning (v :: _) _ _ <- petrol n (steps (MkMeaning [] [] ()) cd)
       pure v

testFVE : run FVE 0 === Just 5
testFVE = Refl

testINC2 : run INC2 1 === Just 3
testINC2 = Refl

testTHR : run THR 2 === Just 3
testTHR = Refl

testLDL : run (LDL [1..4]) 0 === Just [1..4]
testLDL = Refl

testLST : run (SUM ++ LDL [1..4] ++ [APP]) 24 === Just 10
testLST = Refl

testMAP : run (MAP :: PLS :: LDC 1 :: APP :: APP :: LDL [1..3] ++ [APP]) 13
          === Just [2..4]
testMAP = Refl

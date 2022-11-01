||| The content of this module is based on the MSc Thesis
||| Coinductive Formalization of SECD Machine in Agda
||| by Adam Krupička

module Control.SECD

import Data.List.Quantifiers

%default total

data Ty
  = TyInt
  | TyBool
  | TyPair Ty Ty
  | TyList Ty
  | TyFun Ty Ty

%name Ty a,b

data Const : Ty -> Type where
  AnInt : Int -> Const TyInt
  True  : Const TyBool
  False : Const TyBool

fromInteger : Integer -> Const TyInt
fromInteger n = AnInt (cast n)


Stack : Type
Stack = List Ty

Env : Type
Env = List Ty

FunDump : Type
FunDump = List (Ty, Ty)

record State where
  constructor MkState
  stack : Stack
  env   : Env
  dump  : FunDump

data Step  : State -> State -> Type
data Steps : State -> State -> Type

data Step  : State -> State -> Type where
  ||| Load a constant of a base type
  LDC : (c : Const ty) -> MkState s e f `Step` MkState (ty :: s) e f
  ||| Load a value from an address in the environment
  LDA : Any (ty ===) e ->
        MkState s e f `Step` MkState (ty :: s) e f
  ||| Load a recursive function
  LDF : (MkState [] (a :: e) ((a, b) :: f) `Steps` MkState [b] (a :: e) ((a, b) :: f)) ->
        MkState s e f `Step` MkState (TyFun a b :: s) e f
  ||| Apply a function to its argument
  APP : MkState (a :: TyFun a b :: s) e f `Step` MkState (b :: s) e f
  ||| Apply a function to its argument, tail call
  TAP : MkState (a :: TyFun a b :: s) e f `Step` MkState (b :: s) e f
  ||| Return a value from inside a function
  RTN : MkState (b :: s) e ((a, b) :: f) `Step` MkState [ b ] e ((a, b) :: f)
  ||| Load a function for recursive application
  LDR : Any (=== (a,b)) f ->
        MkState s e f `Step` MkState (TyFun a b :: s) e f
  ||| Branch over a boolean
  BCH : (l, r : MkState s e f `Steps` MkState s' e f) ->
        MkState (TyBool :: s) e f `Step` MkState s' e f

  ||| Flip the stack's top values
  FLP : MkState (a :: b :: s) e f `Step` MkState (b :: a :: s) e f

  ||| Nil constructor
  NIL : MkState s e f `Step` MkState (TyList a :: s) e f
  ||| Cons constructor
  CNS : MkState (a :: TyList a :: s) e f `Step` MkState (TyList a :: s) e f
  ||| Head destructor
  HED : MkState (TyList a :: s) e f `Step` MkState (a :: s) e f
  ||| Tail destructor
  TAL : MkState (TyList a :: s) e f `Step` MkState (TyList a :: s) e f

  ||| Pair constructor
  MKP : MkState (a :: b :: s) e f `Step` MkState (TyPair a b :: s) e f
  ||| First pair destructor
  FST : MkState (TyPair a b :: s) e f `Step` MkState (a :: s) e f
  ||| Second pair destructor
  SND : MkState (TyPair a b :: s) e f `Step` MkState (b :: s) e f

  ||| Addition of ints
  ADD : MkState (TyInt :: TyInt :: s) e f `Step` MkState (TyInt :: s) e f
  ||| Subtraction of ints
  SUB : MkState (TyInt :: TyInt :: s) e f `Step` MkState (TyInt :: s) e f
  ||| Multiplication of ints
  MUL : MkState (TyInt :: TyInt :: s) e f `Step` MkState (TyInt :: s) e f

  ||| Structural equality test
  EQB : MkState (a :: a :: s) e f `Step` MkState (TyBool :: s) e f
  ||| Boolean negation
  NOT : MkState (TyBool :: s) e f `Step` MkState (TyBool :: s) e f

data Steps : State -> State -> Type where
  Nil  : Steps s s
  (::) : Step s t -> Steps t u -> Steps s u

data Stepz : State -> State -> Type where
  Lin  : Stepz s s
  (:<) : Stepz s t -> Step t u -> Stepz s u

(<>>) : Stepz s t -> Steps t u -> Steps s u
[<] <>> ts = ts
(ss :< s) <>> ts = ss <>> (s :: ts)

(<><) : Stepz s t -> Steps t u -> Stepz s u
ss <>< [] = ss
ss <>< (t :: ts) = (ss :< t) <>< ts

(++) : Steps s t -> Steps t u -> Steps s u
[] ++ ts = ts
(s :: ss) ++ ts = s :: (ss ++ ts)

NUL : MkState (TyList a :: s) e f `Steps` MkState (TyBool :: s) e f
NUL = [NIL, EQB]

LDL : List Int -> MkState s e f `Steps` MkState (TyList TyInt :: s) e f
LDL vs = go [<NIL] ([<] <>< vs) <>> [] where

  go : MkState s e f `Stepz` MkState (TyList TyInt :: s) e f ->
       SnocList Int ->
       MkState s e f `Stepz` MkState (TyList TyInt :: s) e f
  go acc [<] = acc
  go acc (vs :< v) = go (acc :< LDC (AnInt v) :< CNS) vs

FVE : MkState [] [] [] `Steps` MkState [TyInt] [] []
FVE = [LDC 2, LDC 3, ADD]

FIV : MkState [] [] [] `Steps` MkState [TyInt] [] []
FIV =
  [ LDF [ LDF [LDA (Here Refl), LDA (There (Here Refl)), ADD, RTN ], RTN ]
  , LDC 1
  , APP
  , LDC 2
  , APP
  ]

PLS : MkState s e f `Step` MkState (TyFun TyInt (TyFun TyInt TyInt) :: s) e f
PLS = LDF [ LDF [ LDA (Here Refl)
                , LDA (There (Here Refl))
                , ADD
                , RTN
                ]]

MAP : MkState [] e f `Step` MkState [ TyFun (TyFun a b) (TyFun (TyList a) (TyList b )) ] e f
MAP = LDF [LDF ( LDA (Here Refl)
              :: NUL
              ++ [ BCH [ NIL ]
                       [ LDR (Here Refl), LDA (Here Refl), TAL, APP
                       , LDA (There (Here Refl)), LDA (Here Refl), HED, APP
                       , CNS
                       ]
                 ]
              )]

FLD : MkState [] e f `Step`
      MkState [TyFun (TyFun b (TyFun a b)) (TyFun b (TyFun (TyList a) b))] e f
FLD = LDF [ LDF [ LDF ( LDA (Here Refl)
                     :: NUL
                     ++ [ BCH [ LDA (There (Here Refl)) ]
                              [ LDA (There (There (Here Refl))) -- c
                              , LDA (There (Here Refl)) -- n
                              , APP -- c n
                              , LDA (Here Refl) -- x :: xs
                              , HED
                              , APP -- c n x
                              , LDR (There (Here Refl)) -- foldl c
                              , FLP
                              , APP -- foldl c (c n x)
                              , LDA (Here Refl) -- x :: xs
                              , TAL -- xs
                              , APP -- fold c (c n x) xs
                              ]
                        ])]]

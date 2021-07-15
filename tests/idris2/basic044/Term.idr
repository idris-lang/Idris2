module Term

import Data.Fin

%logging 1
%logging "declare.def" 3

mutual

  data Bdr : (cut : Bool) -> (vars : Nat) -> Type where
    Lam : Bdr cut vars
    Pi  : Chk cut vars -> Bdr cut vars

  -- Checkable terms (i.e. introduction forms)
  data Chk : (cut : Bool) -> (vars : Nat) -> Type where
    Bnd : Bdr cut vars -> Chk cut (S vars) -> Chk cut vars
    Emb : Syn cut vars -> Chk cut n


  -- Synthesisable terms (i.e. elimination forms)
  data Syn : (cut : Bool) -> (vars : Nat) -> Type where
    Var : Fin vars -> Syn cut vars
    App : Syn cut vars -> Chk cut vars -> Syn cut vars
    Cut : Chk True vars -> Typ True vars -> Syn True vars

  Typ : (cut : Bool) -> (vars : Nat) -> Type
  Typ = Chk

Term : Nat -> Type
Term = Chk True

NF : Nat -> Type
NF = Chk False

import Data.List
import Data.List.Elem

%search_timeout 1000

||| A Place has an ID and a number of tokens
data Place : Type where
  MkPlace : (i : Nat) -> (nTokens : Nat) -> Place

||| A transition has a name
data Transition : Type where
  MkTransition : String -> Transition

||| An Input links a Place and a Transition...
data Input : Type where
  MkInput : (from : Place) -> (to : Transition) -> Input

-- Accessor functions for proof
0 inputFrom : Input -> Place
inputFrom (MkInput p t) = p

0 inputTo : Input -> Transition
inputTo (MkInput p t) = t

data SoundInputFrom : Input -> List Place -> Type where
  MkSoundInputFrom : (i : Input)
                     -> (ps : List Place)
                     -> (prf : Elem (inputFrom i) ps)
                     -> SoundInputFrom i ps

data SoundInputTo : Input -> List Transition -> Type where
  MkSoundInputTo : (i : Input)
                   -> (ts : List Transition)
                   -> (prf : Elem (inputTo i) ts)
                   -> SoundInputTo i ts

data SoundInput : Input -> List Place -> List Transition -> Type where
  MkSoundInput : (i : Input)
                 -> (ps : List Place)
                 -> (ts : List Transition)
                 -> (fromOK : SoundInputFrom i ps)
                 -> (toOK   : SoundInputTo   i ts)
                 -> SoundInput i ps ts

data AllInputsSound : List Input -> List Place -> List Transition -> Type where
  NilInputsIsSound : AllInputsSound [] _ _
  ConsIsSound : (headIsSound : SoundInput i ps ts)
                -> (tailIsSound : AllInputsSound is ps ts)
                -> AllInputsSound (i :: is) ps ts

-- Searching here finds the right answer immediately, but then if we don't
-- have a timeout, it takes ages to explore more non-solutions! So we cut off
-- after a second
tailIsNotSound : (contra : (AllInputsSound is ps ts -> Void))
                 -> AllInputsSound (i :: is) ps ts
                 -> Void

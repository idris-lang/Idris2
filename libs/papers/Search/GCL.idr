||| The content of this module is based on the paper
||| Applications of Applicative Proof Search
||| by Liam O'Connor
||| https://doi.org/10.1145/2976022.2976030

module Search.GCL

import Data.So
import Data.Nat
import Data.Fuel
import Data.List.Lazy
import Data.List.Quantifiers
import Data.List.Lazy.Quantifiers
import Decidable.Equality

import public Search.CTL

%default total

||| Weaken a Dec to a Bool.
public export
weaken : Dec _ -> Bool
weaken (Yes _) = True
weaken (No  _) = False

parameters (Sts : Type)

  ------------------------------------------------------------------------
  -- Types and operational semantics

  mutual
    ||| Guarded Command Language
    public export
    data GCL : Type where
      IF : (gs : List GUARD) -> GCL

      DOT : GCL -> GCL -> GCL

      DO : (gs : List GUARD) -> GCL

      UPDATE : (u : Sts -> Sts) -> GCL

      ||| Termination
      SKIP : GCL

    ||| A predicate
    public export
    Pred : Type
    Pred = (st : Sts) -> Bool

    ||| Guards are checks on the current state
    public export
    record GUARD where
      constructor MkGUARD
      ||| The check to confirm
      g : Pred
      ||| The current state
      x : GCL

  public export
  Uninhabited (IF _ === SKIP) where
    uninhabited Refl impossible

  public export
  Uninhabited (DOT _ _ === SKIP) where
    uninhabited Refl impossible

  public export
  Uninhabited (DO _ === SKIP) where
    uninhabited Refl impossible

  public export
  Uninhabited (UPDATE _ === SKIP) where
    uninhabited Refl impossible

  ||| Prove that the given program terminated (i.e. reached a `SKIP`).
  public export
  isSkip : (l : GCL) -> Dec (l === SKIP)
  isSkip (IF xs)     = No absurd
  isSkip (DOT y z)   = No absurd
  isSkip (DO xs)     = No absurd
  isSkip (UPDATE uf) = No absurd
  isSkip SKIP        = Yes Refl

  ||| Operational semantics of GCL.
  ||| (curried version to pass the termination checker)
  public export
  ops' : GCL -> Sts -> List (GCL, Sts)
  ops' SKIP st = []
  ops' (UPDATE u) st = [(SKIP, u st)]
  ops' (DOT SKIP y) st = [(y, st)]
  ops' (DOT x y) st = mapFst (`DOT` y) <$> ops' x st
  ops' (IF gs) st = map (\ aGuard => (aGuard.x, st)) $
                    filter (\ aGuard => aGuard.g st) gs

  ops' (DO gs) st with (map (\ aG => ((DOT aG.x (DO gs)), st)) $
                        filter (\ aG => aG.g st) gs)
    _ | [] = [(SKIP, st)]
    _ | ys = ys

  ||| Operational semantics of GCL.
  public export
  ops : (GCL, Sts) -> List (GCL, Sts)
  ops (l, st) = ops' l st

  ||| We can convert a GCL program to a transition digram by using the program
  ||| as the state and the operational semantics as the transition function.
  public export
  gclToDiag : GCL -> Diagram GCL Sts
  gclToDiag p = TD ops p


  ------------------------------------------------------------------------
  -- Control Structures

  ||| While loops are GCL do loops with a single guard.
  public export
  while : Pred -> GCL -> GCL
  while g x = DO [MkGUARD g x]

  ||| Await halts progress unless the predicate is satisfied.
  public export
  await : Pred -> GCL
  await g = IF [MkGUARD g SKIP]

  ||| If statements translate into GCL if statements by having an unmodified and
  ||| a negated version of the predicate in the list of `IF` GCL statements.
  public export
  ifThenElse : (g : Pred) -> (x : GCL) -> (y : GCL) -> GCL
  ifThenElse g x y = IF [MkGUARD g x, MkGUARD (not . g) y]


------------------------------------------------------------------------
-- Example: Peterson's Algorithm

public export
record State where
  constructor MkState
  -- shared state: intent1, intent2, and turn
  intent1, intent2 : Bool
  turn : Nat
  -- is the current state in its critical section?
  inCS1, inCS2 : Bool

||| First critical section
public export
CS1 : GCL State
CS1 =
  DOT State
    (UPDATE State (\st => { inCS1 := True } st))
    (DOT State
      (SKIP State)
      (UPDATE State (\st => { inCS1 := False } st))
      )

||| Second critical section
public export
CS2 : GCL State
CS2 =
  DOT State
    (UPDATE State (\st => { inCS2 := True } st))
    (DOT State
      (SKIP State)
      (UPDATE State (\st => { inCS2 := False } st))
      )

||| First Peterson's algorithm process
public export
petersons1 : GCL State
petersons1 =
  DOT State
    (UPDATE State (\st => { intent1 := True } st))
    (DOT State
      (UPDATE State (\st => { turn := 1 } st))
      (DOT State
        (await State (\st => (not st.intent2) || (weaken (decEq st.turn 0))))
        (DOT State
          CS1
          (UPDATE State (\st => { intent1 := False } st))
          )))

||| Second Peterson's algorithm process
public export
petersons2 : GCL State
petersons2 =
  DOT State
    (UPDATE State (\st => { intent2 := True } st))
    (DOT State
      (UPDATE State (\st => { turn := 0 } st))
      (DOT State
        (await State (\st => (not st.intent1) || (weaken (decEq st.turn 1))))
        (DOT State
          CS2
          (UPDATE State (\st => { intent2 := False } st))
          )))

||| The parallel composition of the two Peterson's processes, to be
||| model-checked.
public export
petersons : Diagram (GCL State, GCL State) State
petersons = (gclToDiag State petersons1) `pComp` (gclToDiag State petersons2)


------------------------------------------------------------------------
-- Properties to verify

||| Type-level decider for booleans.
public export
IsTT : (b : Bool) -> Dec (So b)
IsTT True = Yes Oh
IsTT False = No absurd


||| Mutual exclusion, i.e. both critical sections not simultaneously active.
public export
Mutex : Formula ? ?
Mutex =
  AlwaysGlobal (GCL State, GCL State) State
      (Guarded (GCL State, GCL State) State
          (\p,_ => So (not (p.inCS1 && p.inCS2))))

||| Model-check (search) whether the mutex condition is satisfied.
public export
checkMutex : MC (GCL State, GCL State) State Mutex
checkMutex =
  agSearch (GCL State, GCL State) State
      (now (GCL State, GCL State) State
          (\p,_ => fromDec $ IsTT _))
                              --  ^ (not (p .inCS1 && (Delay (p .inCS2)))

||| Starvation freedom
public export
SF : Formula ? ?
SF =
  let guardCS1 = Guarded (GCL State, GCL State) State (\p,_ => So (p.inCS1))
      guardCS2 = Guarded (GCL State, GCL State) State (\p,_ => So (p.inCS2))
  in AND' (GCL State, GCL State) State
      (AlwaysFinally (GCL State, GCL State) State guardCS1)
      (AlwaysFinally (GCL State, GCL State) State guardCS2)

||| Model-check (search) whether starvation freedom holds.
public export
checkSF : MC (GCL State, GCL State) State SF
checkSF =
  let mcAndFst = afSearch (GCL State, GCL State) State
                     (now (GCL State, GCL State) State
                        (\p,_ => fromDec $ IsTT _))
                                     -- p.inCS1 ^
      mcAndSnd = afSearch (GCL State, GCL State) State
                     (now (GCL State, GCL State) State
                        (\p,_ => fromDec $ IsTT _))
                                     -- p.inCS2 ^
  in mcAND' (GCL State, GCL State) State mcAndFst mcAndSnd


||| Deadlock freedom, aka. termination for all possible paths/traces
public export
Termination : Formula ? ?
Termination =
  AlwaysFinally (GCL State, GCL State) State
       (Guarded (GCL State, GCL State) State
          (\_,l => allSkip l))
  where
    allSkip : (l : (GCL State, GCL State)) -> Type
    allSkip l = (fst l === SKIP State, snd l === SKIP State)

||| Model-check (search) whether termination holds.
public export
checkTermination : MC (GCL State, GCL State) State Termination
checkTermination =
  afSearch (GCL State, GCL State) State
      (now (GCL State, GCL State) State
          (\_,l => MkHDec (isTerm l) (sound l)))
  where
    -- l should be auto-implicit, but we can't search for that here
    isTerm : (l : (GCL State, GCL State)) -> Bool
    isTerm (a, b) =
      (weaken $ isSkip State a) && (weaken $ isSkip State b)

    sound :  (l : (GCL State, GCL State))
          -> So (isTerm l)
          -> (fst l === SKIP State, snd l === SKIP State)
    sound (a, b) _ with (isSkip State a) | (isSkip State b)
      sound (a, b) _  | (Yes p) | (Yes q) = (p, q)
      sound (a, b) Oh | (Yes p) | (No _)  impossible
      sound (a, b) Oh | (No _)  | _       impossible


||| Initial state for model-checking Peterson's algorithm.
public export
init : State
init = MkState False False 0 False False
        -- intent1 intent2 turn inCS1 inCS2

||| The computational tree for the two Peterson's processes.
public export
tree : CT (GCL State, GCL State) State
tree = model (GCL State, GCL State) State petersons init

||| The Critical Section Problem:
||| 1) a process's critical section (CS) is only ever accessed by that process
|||    and no other
||| 2) any process which wishes to gain access to its CS eventually
|||    does so
||| 3) the composition of the processes is deadlock free
|||    (we use a stronger requirement: that all process composition must
|||    terminate successfully)
public export
CSP : Type
CSP = (arg : Nat **
        AND' (GCL State, GCL State) State
          (\depth, tree => Mutex depth tree)              -- mutually exclusive
          (\depth, tree =>
            AND' (GCL State, GCL State) State
              (\depth, tree => SF depth tree)             -- starvation free
              (\depth, tree => Termination depth tree)    -- completed
              depth tree)
        arg GCL.tree)

||| A `Prop` (property) containing all the conditions necessary for proving that
||| Peterson's Algorithm is a correct solution to the Critical Section Problem.
||| When evaluated (e.g. through the `auto` search in a `Properties.check`
||| call; specifically `runProp`), it will produce the required proof (which is
||| **very** big).
public export
checkPetersons : Prop ? CSP
checkPetersons = exists $
                  (mcAND' (GCL State, GCL State) State
                    checkMutex
                    (mcAND' (GCL State, GCL State) State
                      checkSF
                      checkTermination
                      ))
                   tree


{- N.B.: commenting this in causes the type-checking of this file to take ~2
 -       minutes and ~4 GB of RAM
 -

||| Prove that Peterson's Algorithm is a solution to the Critical Section
||| Problem. This evaluates the `checkPetersons` property to obtain a proof (at
||| a search depth of 1000!), at which point we can show that it is
||| depth-invariant.
|||
||| /!\       CAUTION: THIS IS **EXTREMELY** SLOW + RESOURCE INTENSIVE       /!\
||| /!\ Attempt at evaluation did not complete after 3hrs and 57.6 GB of RAM /!\
public export
petersonsCorrect : Models ? ?
                    GCL.tree
                    (AND' ? ?
                      Mutex
                      (AND' ? ?
                        SF
                        Termination
                        ))
petersonsCorrect =
  diModels (GCL State, GCL State) State
           (snd (check @{%search} (limit 1000) checkPetersons @{Oh}))

 -}



------------------------------------------------------------------------
-- Example: Dekker's Algorithm

||| First Dekker's algorithm process
public export
dekkers1 : GCL State
dekkers1 =
  DOT _
    (UPDATE _ (\st => { intent1 := True } st))
    (DOT _
      (while _ (\st => st.intent2)
        (IF _ [ (MkGUARD _ (\st => weaken $ decEq st.turn 0) (SKIP _))
              , (MkGUARD _ (\st => weaken $ decEq st.turn 1)
                           (DOT _
                            (UPDATE _ (\st => { intent1 := False } st))
                            (DOT _
                              (await _ (\st => weaken $ decEq st.turn 0))
                              (UPDATE _ (\st => { intent1 := True } st))
                              )))
              ]
        ))
        (DOT _
          CS1
          (DOT _
            (UPDATE _ (\st => { turn := 1 } st))
            (UPDATE _ (\st => { intent1 := False } st))
    )))

||| First Dekker's algorithm process
public export
dekkers2 : GCL State
dekkers2 =
  DOT _
    (UPDATE _ (\st => { intent2 := True } st))
    (DOT _
      (while _ (\st => st.intent1)
        (IF _ [ (MkGUARD _ (\st => weaken $ decEq st.turn 1) (SKIP _))
              , (MkGUARD _ (\st => weaken $ decEq st.turn 0)
                           (DOT _
                            (UPDATE _ (\st => { intent2 := False } st))
                            (DOT _
                              (await _ (\st => weaken $ decEq st.turn 1))
                              (UPDATE _ (\st => { intent2 := True } st))
                              )))
              ]
        ))
        (DOT _
          CS2
          (DOT _
            (UPDATE _ (\st => { turn := 0 } st))
            (UPDATE _ (\st => { intent2 := False } st))
    )))

||| The parallel composition of the two Dekker's processes, to be model-checked.
public export
dekkers : Diagram (GCL State, GCL State) State
dekkers = (gclToDiag _ dekkers1) `pComp` (gclToDiag _ dekkers2)

||| An attempt at finding a violation of Mutual Exclusion.
||| THIS WILL NOT FIND A PROOF due to the lack of fairness in the unfolding of
||| the traces. Dekker's algorithm requires fair scheduling in order to be
||| correct, but since we don't have that, we cannot find a proof that no
||| violations of mutex exist.
|||
||| /!\ Trying to evaluate this did not finish after 10 minutes /!\
public export
checkDekkers : HDec ?
checkDekkers =
  efSearch _ _
    (now _ _ (\p, _ => (fromDec $ IsTT (p.inCS1 && p.inCS2))))
    (model _ _ dekkers init) 100


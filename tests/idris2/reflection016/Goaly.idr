import Language.Reflection

%default total

%macro
failyGoaly : Nat -> Elab a
failyGoaly _ = do
  Just goal <- goal
     | Nothing => fail "no goal at all"
  logSugaredTerm "bug.lostgoal" 0 "the goal" goal
  case goal of
    `(Prelude.Types.Nat) => fail "good goal; intensional (expected) failure"
    _                    => fail "unexpected goal"

%language ElabReflection

x : Nat
x = failyGoaly 5

%macro
choosing : Elab a
choosing = do
  Just goal <- goal
    | Nothing => fail "no goal at all"
  logSugaredTerm "bug.lostgoal.uns" 0 "the goal" goal
  case goal of
    `(Prelude.Types.Nat)                                  => check `(5)
    IPi _ _ _ _ `(Prelude.Types.Nat) `(Prelude.Types.Nat) => check `((+6))
    _                                                     => fail "unexpected goal"

chV : Nat -> Nat
chV x = x + choosing

chF : Nat -> Nat
chF = choosing

chF' : Nat -> Nat
chF' x = choosing x

%macro
goaly : Nat => Elab $ Nat -> a
goaly = do
  Just g <- goal
    | Nothing => fail "no goal"
  case g of
    IPi _ _ _ _ _ res => case res of
                           `(Prelude.Types.Nat) => check `(S)
                           IHole _ _            => fail "unknown resulting type of a function"
                           _                    => fail "unsupported resulting type of a function"
    IHole _ n         => fail "goal is hole \{show n}"
    _                 => do logSugaredTerm "nogoal" 0 "goal" g
                            fail "can't manage the given result type"

%language ElabReflection

knownCorrectGoal : Nat -> Nat
knownCorrectGoal = goaly @{Z}

knownCorrectGoal' : Nat -> Nat
knownCorrectGoal' = S . the (Nat -> Nat) (goaly @{Z})

knownIncorrectGoal : Nat -> String
knownIncorrectGoal = goaly @{Z}

holeInGoal : Nat -> ?
holeInGoal = goaly @{Z}

uknownOrNoHole : ?
uknownOrNoHole = goaly @{Z}

knownResultInGoal : Nat -> Nat
knownResultInGoal = S . goaly @{Z}

nowYetKnownResultInGoal : Nat -> Nat
nowYetKnownResultInGoal = goaly @{Z} . S

goalInMap : List Nat -> List Nat
goalInMap = map $ goaly @{Z}

%macro
goaly' : Nat -> Elab $ Nat -> a
goaly' _ = do
  Just g <- goal
    | Nothing => fail "no goal"
  case g of
    IPi _ _ _ _ _ res => case res of
                           `(Prelude.Types.Nat) => check `(S)
                           IHole _ _            => fail "unknown resulting type of a function"
                           _                    => fail "unsupported resulting type of a function"
    IHole _ n         => fail "goal is hole \{show n}"
    _                 => do logSugaredTerm "nogoal" 0 "goal" g
                            fail "can't manage the given result type"

noStart : String -> String
noStart = goaly' 4

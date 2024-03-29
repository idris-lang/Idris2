nats : List Nat -> List Nat
nats ns = the (List Nat) ns

singletonRange : nats [1..1] = nats [1]
singletonRange = Refl

basicIncreasingRange : nats [1..3] = nats [1, 2 , 3]
basicIncreasingRange = Refl

basicDecreasingRange : nats [3..1] = nats [3, 2, 1]
basicDecreasingRange = Refl


increasingRangeWithStep : nats [3, 5..11] = nats [3, 5, 7, 9, 11]
increasingRangeWithStep = Refl

increaingRangeWithStepEmpty : nats [3, 5..1] = nats []
increaingRangeWithStepEmpty = Refl

singletonRangeWithStep : nats [3, 4..3] = nats [3]
singletonRangeWithStep = Refl

zeroStepEmptyList : nats [3, 3..5] = nats []
zeroStepEmptyList = Refl

zeroStepWhenBoundEqual : nats [1, 1..1] = nats [1]
zeroStepWhenBoundEqual = Refl

decreasingRangeWithStep : nats [11, 8..1] = nats [11, 8, 5, 2]
decreasingRangeWithStep = Refl

decreasingRangeWithStepEmpty : nats [9, 8..10] = nats []
decreasingRangeWithStepEmpty = Refl

decreasingSingletonRangeWithStep : nats [9, 8..9] = nats [9]
decreasingSingletonRangeWithStep = Refl

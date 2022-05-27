chars : List Char -> List Char
chars = the (List Char)

singletonRange : chars ['1'..'1'] = chars ['1']
singletonRange = Refl

basicIncreasingRange : chars ['1'..'3'] = chars ['1', '2', '3']
basicIncreasingRange = Refl

basicDecreasingRange : chars ['3'..'1'] = chars ['3', '2', '1']
basicDecreasingRange = Refl


increasingRangeWithStep : chars ['3', '5'..';'] = chars ['3', '5', '7', '9', ';']
increasingRangeWithStep = Refl

increaingRangeWithStepEmpty : chars ['3', '5'..'1'] = chars []
increaingRangeWithStepEmpty = Refl

singletonRangeWithStep : chars ['3', '4'..'3'] = chars ['3']
singletonRangeWithStep = Refl

zeroStepEmptyList : chars ['3', '3'..'5'] = chars []
zeroStepEmptyList = Refl

zeroStepWhenBoundEqual : chars ['1', '1'..'1'] = chars ['1']
zeroStepWhenBoundEqual = Refl

decreasingRangeWithStep : chars [';', '8'..'1'] = chars [';', '8', '5', '2']
decreasingRangeWithStep = Refl

decreasingRangeWithStepEmpty : chars ['9', '8'..':'] = chars []
decreasingRangeWithStepEmpty = Refl

decreasingSingletonRangeWithStep : chars ['9', '8'..'9'] = chars ['9']
decreasingSingletonRangeWithStep = Refl

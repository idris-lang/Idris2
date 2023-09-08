module C

import B

public export
bar : {default defaultRec rec : Rec} -> Char
bar {rec} = field rec

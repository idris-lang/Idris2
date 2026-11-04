%default total

K : Type
K = K -> Void

absurd : K
absurd k = k k

contradiction : Void
contradiction = absurd absurd

module Data.Void

export
persistentVoid : (0 x : Void) -> Void
persistentVoid _ impossible

export
absurdity : Uninhabited t => (0 _ : t) -> s
absurdity x = absurd (persistentVoid (uninhabited x))

export
absurdSince : (Uninhabited t) => (0 _ : x -> t) -> (x -> s)
absurdSince since x = absurdity (since x)

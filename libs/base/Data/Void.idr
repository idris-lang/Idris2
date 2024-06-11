module Data.Void

export
absurdity : Uninhabited t => (0 _ : t) -> s
absurdity x = void (uninhabited x)

export
contradiction : Uninhabited t => (0 _ : x -> t) -> (x -> s)
contradiction since x = absurdity (since x)

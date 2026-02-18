module Issue1988

data D : Type where Abs : (D -> Void) -> D

app : D -> D -> Void
app (Abs f) d = f d

omega : D
omega = Abs (\x => app x x)

total
Omega : Void
Omega = app omega omega

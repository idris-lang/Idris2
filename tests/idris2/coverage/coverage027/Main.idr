data X = X1 | X2

f : (0 _ : X) -> Void
f X1 impossible

g : (0 _ : X) -> Void
g X1 impossible
g X2 impossible


data Y = Y1 Void | Y2

h : (0 _ : Y) -> Void
h (Y1 _) impossible

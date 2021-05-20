data SnocList ty = Empty | Snoc (Main.SnocList ty) ty

reverseSnoc : Main.SnocList ty -> List ty
reverseSnoc Empty = []
reverseSnoc (Snoc xs x) = x :: reverseSnoc xs

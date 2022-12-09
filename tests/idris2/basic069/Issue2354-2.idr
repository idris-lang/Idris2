test : Stream Bool
test = (if True then id else (Prelude.(::) True)) $ the (List Bool) []

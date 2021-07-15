data EitherOrBoth a b = Left a | Rigth b | Both a b

foo : EitherOrBoth a b -> ()

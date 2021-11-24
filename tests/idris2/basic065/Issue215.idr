In : (x : a) -> (l : List a) -> Type
In x [] = Void
In x (x' :: xs) = (x' = x) `Either` In x xs

appendEmpty : (xs : List a) -> xs ++ [] = xs
appendEmpty [] = Refl
appendEmpty (x :: xs) = rewrite appendEmpty xs in Refl

in_app_iff : {l : List b} -> {l' : List b} -> In a (l++l') -> (In a l `Either` In a l')
in_app_iff {l = []} {  l' = []} x = Left x
in_app_iff {l = []} {  l' = (y :: xs)} x = Right x
in_app_iff {l = (y::xs)} {  l' = []} x = rewrite sym (appendEmpty xs) in Left x
in_app_iff {l = (y::xs)} {l' = (z::ys)} (Left prf) = Left (Left prf)
in_app_iff {l = (y::xs)} {l' = (z::ys)} (Right prf) =
                                          let induc : Either (In a xs) (Either (z = a) (In a ys))= in_app_iff {l = xs} {l' = z :: ys} prf  in
                                          case induc of
                                                (Left l) => Left $ Right l
                                                (Right r) => Right r


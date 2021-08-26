%default total

fix : Void
fix = case the (Either () Void) (Left ()) of
        Left () => fix
        Right p => absurd p

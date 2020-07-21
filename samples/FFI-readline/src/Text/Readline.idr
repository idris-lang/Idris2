module Text.Readline

rlib : String -> String
rlib fn = "C:" ++ fn ++ ",libidrisreadline"

%foreign (rlib "getString")
export
getString : Ptr String -> String

%foreign (rlib "mkString")
export
mkString : String -> Ptr String

%foreign (rlib "nullString")
export
nullString : Ptr String

%foreign (rlib "isNullString")
prim__isNullString : Ptr String -> Int

export
isNullString : Ptr String -> Bool
isNullString str = not $ prim__isNullString str == 0

%foreign (rlib "readline")
prim__readline : String -> PrimIO (Ptr String)

export
readline : HasIO io => String -> io (Maybe String)
readline s
    = do mstr <- primIO $ prim__readline s
         pure $ if isNullString mstr
                   then Nothing
                   else Just (getString mstr)

%foreign (rlib "add_history")
prim__add_history : String -> PrimIO ()

export
addHistory : HasIO io => String -> io ()
addHistory s = primIO $ prim__add_history s

%foreign (rlib "idrisrl_setCompletion")
prim__setCompletion : (String -> Int -> PrimIO (Ptr String)) -> PrimIO ()

export
setCompletionFn : HasIO io => (String -> Int -> IO (Maybe String)) -> io ()
setCompletionFn fn
    = primIO $ prim__setCompletion $ \s, i => toPrim $
          do mstr <- fn s i
             case mstr of
                  Nothing => pure nullString
                  Just str => pure (mkString str)

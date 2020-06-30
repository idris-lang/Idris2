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
prim_isNullString : Ptr String -> Int

export
isNullString : Ptr String -> Bool
isNullString str = if prim_isNullString str == 0 then False else True

%foreign (rlib "readline")
prim_readline : String -> PrimIO (Ptr String)

export
readline : HasIO io => String -> io (Maybe String)
readline s
    = do mstr <- primIO $ prim_readline s
         if isNullString mstr
            then pure $ Nothing
            else pure $ Just (getString mstr)

%foreign (rlib "add_history")
prim_add_history : String -> PrimIO ()

export
addHistory : HasIO io => String -> io ()
addHistory s = primIO $ prim_add_history s

%foreign (rlib "idrisrl_setCompletion")
prim_setCompletion : (String -> Int -> PrimIO (Ptr String)) -> PrimIO ()

export
setCompletionFn : HasIO io => (String -> Int -> IO (Maybe String)) -> io ()
setCompletionFn fn
    = primIO $ prim_setCompletion $ \s, i => toPrim $
          do mstr <- fn s i
             case mstr of
                  Nothing => pure nullString
                  Just str => pure (mkString str)

module System.Readline

support : String -> String
support fn = "C:" ++ fn ++ ", libidris2_support"

%foreign (support "idris2_getString")
getString : Ptr String -> String

%foreign (support "idris2_mkString")
mkString : String -> Ptr String

%foreign (support "idris2_nullString")
nullString : Ptr String

%foreign (support "idris2_isNullString")
prim__isNullString : Ptr String -> Int

isNullString : Ptr String -> Bool
isNullString str = not $ prim__isNullString str == 0

%foreign (support "readline")
prim__readline : String -> PrimIO (Ptr String)

export
readline : HasIO io => String -> io (Maybe String)
readline s
    = do mstr <- primIO $ prim__readline s
         pure $ if isNullString mstr
                   then Nothing
                   else Just (getString mstr)

%foreign (support "add_history")
prim__add_history : String -> PrimIO ()

export
addHistory : HasIO io => String -> io ()
addHistory s = primIO $ prim__add_history s

%foreign (support "idris2_setCompletion")
prim__setCompletion : (String -> Int -> PrimIO (Ptr String)) -> PrimIO ()

export
setCompletionFn : HasIO io => (String -> Int -> IO (Maybe String)) -> io ()
setCompletionFn fn
    = primIO $ prim__setCompletion $ \s, i => toPrim $ do
        mstr <- fn s i
        case mstr of
             Nothing => pure nullString
             Just str => pure (mkString str)

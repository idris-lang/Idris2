module Libraries.Utils.Scheme

export
data ForeignObj : Type where [external]

%foreign "scheme:blodwen-eval-scheme"
prim__evalScheme : String -> ForeignObj

%foreign "scheme:blodwen-eval-okay"
prim__evalOkay : ForeignObj -> Int

%foreign "scheme:blodwen-get-eval-result"
prim__evalResult : ForeignObj -> ForeignObj

%foreign "scheme:blodwen-debug-scheme"
prim__debugScheme : ForeignObj -> PrimIO ()

%foreign "scheme:blodwen-is-number"
prim_isNumber : ForeignObj -> Int

%foreign "scheme:blodwen-is-integer"
prim_isInteger : ForeignObj -> Int

%foreign "scheme:blodwen-is-float"
prim_isFloat : ForeignObj -> Int

%foreign "scheme:blodwen-is-char"
prim_isChar : ForeignObj -> Int

%foreign "scheme:blodwen-is-string"
prim_isString : ForeignObj -> Int

%foreign "scheme:blodwen-is-procedure"
prim_isProcedure : ForeignObj -> Int

%foreign "scheme:blodwen-is-symbol"
prim_isSymbol : ForeignObj -> Int

%foreign "scheme:blodwen-is-nil"
prim_isNil : ForeignObj -> Int

%foreign "scheme:blodwen-is-pair"
prim_isPair : ForeignObj -> Int

%foreign "scheme:blodwen-is-vector"
prim_isVector : ForeignObj -> Int

%foreign "scheme:blodwen-is-box"
prim_isBox : ForeignObj -> Int

export
isNumber : ForeignObj -> Bool
isNumber x = prim_isNumber x == 1

export
isInteger : ForeignObj -> Bool
isInteger x = prim_isInteger x == 1

export
isFloat : ForeignObj -> Bool
isFloat x = prim_isFloat x == 1

export
isChar : ForeignObj -> Bool
isChar x = prim_isChar x == 1

export
isString : ForeignObj -> Bool
isString x = prim_isString x == 1

export
isProcedure : ForeignObj -> Bool
isProcedure x = prim_isProcedure x == 1

export
isSymbol : ForeignObj -> Bool
isSymbol x = prim_isSymbol x == 1

export
isNil : ForeignObj -> Bool
isNil x = prim_isNil x == 1

export
isPair : ForeignObj -> Bool
isPair x = prim_isPair x == 1

export
isVector : ForeignObj -> Bool
isVector x = prim_isVector x == 1

export
isBox : ForeignObj -> Bool
isBox x = prim_isBox x == 1

-- The below are all 'unsafe' because they rely on having done the relevant
-- check above first
%foreign "scheme:blodwen-id"
export
unsafeGetInteger : ForeignObj -> Integer

%foreign "scheme:blodwen-id"
export
unsafeGetString : ForeignObj -> String

%foreign "scheme:blodwen-id"
export
unsafeGetFloat : ForeignObj -> Double

%foreign "scheme:blodwen-id"
export
unsafeGetChar : ForeignObj -> Char

%foreign "scheme:car"
export
unsafeFst : ForeignObj -> ForeignObj

%foreign "scheme:cdr"
export
unsafeSnd : ForeignObj -> ForeignObj

%foreign "scheme:blodwen-apply"
export
unsafeApply : ForeignObj -> ForeignObj -> ForeignObj

%foreign "scheme:blodwen-force"
export
unsafeForce : ForeignObj -> ForeignObj

%foreign "scheme:blodwen-vector-ref"
export
unsafeVectorRef : ForeignObj -> Integer -> ForeignObj

%foreign "scheme:blodwen-unbox"
export
unsafeUnbox : ForeignObj -> ForeignObj

%foreign "scheme:blodwen-vector-length"
export
unsafeVectorLength : ForeignObj -> Integer

%foreign "scheme:blodwen-vector-list"
export
unsafeVectorToList : ForeignObj -> List ForeignObj

%foreign "scheme:blodwen-make-symbol"
export
makeSymbol : String -> ForeignObj

%foreign "scheme:blodwen-read-symbol"
export
unsafeReadSymbol : ForeignObj -> String

export
evalSchemeStr : String -> IO (Maybe ForeignObj)
evalSchemeStr exp
    = let obj = prim__evalScheme exp in
          if prim__evalOkay obj == 1
             then pure $ Just (prim__evalResult obj)
             else pure Nothing

export
debugScheme : ForeignObj -> IO ()
debugScheme obj = primIO $ prim__debugScheme obj

public export
data Direction = Write | Readback

public export
data SchemeObj : Direction -> Type where
     Null : SchemeObj t
     Cons : SchemeObj t -> SchemeObj t -> SchemeObj t
     IntegerVal : Integer -> SchemeObj t
     FloatVal : Double -> SchemeObj t
     StringVal : String -> SchemeObj t
     CharVal : Char -> SchemeObj t
     Symbol : String -> SchemeObj t
     Box : SchemeObj t -> SchemeObj t
     Vector : Integer -> List (SchemeObj t) -> SchemeObj t
        -- ^ this is convenient for us since all our vectors start with a
        -- tag, but not for a general library

     Procedure : ForeignObj -> SchemeObj Readback

     Define : String -> SchemeObj Write -> SchemeObj Write
     Var : String -> SchemeObj Write
     Lambda : List String -> SchemeObj Write -> SchemeObj Write
     Let : String -> SchemeObj Write -> SchemeObj Write -> SchemeObj Write
     If : SchemeObj Write -> SchemeObj Write -> SchemeObj Write ->
          SchemeObj Write
     Case : SchemeObj Write ->
            List (SchemeObj Write, SchemeObj Write) ->
            Maybe (SchemeObj Write) ->
            SchemeObj Write
     Cond : List (SchemeObj Write, SchemeObj Write) ->
            Maybe (SchemeObj Write) ->
            SchemeObj Write
     Apply : SchemeObj Write -> List (SchemeObj Write) -> SchemeObj Write

export
evalSchemeObj : SchemeObj Write -> IO (Maybe ForeignObj)
evalSchemeObj obj
    = do let str = toString obj
         evalSchemeStr str
  where
    showSep : String -> List String -> String
    showSep sep [] = ""
    showSep sep [x] = x
    showSep sep (x :: xs) = x ++ sep ++ showSep sep xs

    toString : SchemeObj Write -> String
    toString Null = "'()"
    toString (Cons x y) = "(cons " ++ toString x ++ " " ++ toString y ++ ")"
    toString (IntegerVal x) = show x
    toString (FloatVal x) = show x
    toString (StringVal x) = show x
    toString (CharVal x)
       = if (the Int (cast x) >= 32 && the Int (cast x) < 127)
            then "#\\" ++ cast x
            else "(integer->char " ++ show (the Int (cast x)) ++ ")"
    toString (Symbol x) = "'" ++ x
    toString (Vector i xs) = "(vector " ++ show i ++ " " ++ showSep " " (map toString xs) ++ ")"
    toString (Box x) = "(box " ++ toString x ++ ")"
    toString (Define x body) = "(define (" ++ x ++ ") " ++ toString body ++ ")"
    toString (Var x) = x
    toString (Lambda xs x)
        = "(lambda (" ++ showSep " " xs ++ ") " ++ toString x ++ ")"
    toString (Let var val x)
        = "(let ((" ++ var ++ " " ++ toString val ++ ")) " ++ toString x ++ ")"
    toString (If x t e)
        = "(if " ++ toString x ++ " " ++ toString t ++ " " ++ toString e ++ ")"
    toString (Case x alts def)
        = "(case " ++ toString x ++ " " ++
              showSep " " (map showAlt alts) ++
              showDef def ++ ")"
      where
        showAlt : (SchemeObj Write, SchemeObj Write) -> String
        showAlt (opt, go)
           = "((" ++ toString opt ++ ") " ++ toString go ++ ")"

        showDef : Maybe (SchemeObj Write) -> String
        showDef Nothing = ""
        showDef (Just e) = " (else " ++ toString e ++ ")"
    toString (Cond alts def)
        = "(cond " ++
              showSep " " (map showAlt alts) ++
              showDef def ++ ")"
      where
        showAlt : (SchemeObj Write, SchemeObj Write) -> String
        showAlt (opt, go)
           = "(" ++ toString opt ++ " " ++ toString go ++ ")"

        showDef : Maybe (SchemeObj Write) -> String
        showDef Nothing = ""
        showDef (Just e) = " (else " ++ toString e ++ ")"
    toString (Apply x xs)
        = "(" ++ toString x ++ " " ++ showSep " " (map toString xs) ++ ")"

export
decodeObj : ForeignObj -> SchemeObj Readback
decodeObj obj
    = if isInteger obj then IntegerVal (unsafeGetInteger obj)
      else if isVector obj then Vector (unsafeGetInteger (unsafeVectorRef obj 0))
                                       (readVector (unsafeVectorLength obj) 1 obj)
      else if isPair obj then Cons (decodeObj (unsafeFst obj))
                                   (decodeObj (unsafeSnd obj))
      else if isFloat obj then FloatVal (unsafeGetFloat obj)
      else if isString obj then StringVal (unsafeGetString obj)
      else if isChar obj then CharVal (unsafeGetChar obj)
      else if isSymbol obj then Symbol (unsafeReadSymbol obj)
      else if isProcedure obj then Procedure obj
      else if isBox obj then Box (decodeObj (unsafeUnbox obj))
      else Null
  where
    readVector : Integer -> Integer -> ForeignObj -> List (SchemeObj Readback)
    readVector len i obj
        = if len == i
             then []
             else decodeObj (unsafeVectorRef obj i) ::
                     readVector len (i + 1) obj

public export
interface Scheme a where
  toScheme : a -> SchemeObj Write
  fromScheme : SchemeObj Readback -> Maybe a

export
evalScheme : Scheme a => a -> IO (Maybe ForeignObj)
evalScheme = evalSchemeObj . toScheme

export
decode : Scheme a => ForeignObj -> Maybe a
decode = fromScheme . decodeObj

export
Scheme Integer where
  toScheme x = IntegerVal x

  fromScheme (IntegerVal x) = Just x
  fromScheme _ = Nothing

export
Scheme Int where
  toScheme x = IntegerVal (cast x)

  fromScheme (IntegerVal x) = Just (cast x)
  fromScheme _ = Nothing

export
Scheme Int8 where
  toScheme x = IntegerVal (cast x)

  fromScheme (IntegerVal x) = Just (cast x)
  fromScheme _ = Nothing

export
Scheme Int16 where
  toScheme x = IntegerVal (cast x)

  fromScheme (IntegerVal x) = Just (cast x)
  fromScheme _ = Nothing

export
Scheme Int32 where
  toScheme x = IntegerVal (cast x)

  fromScheme (IntegerVal x) = Just (cast x)
  fromScheme _ = Nothing

export
Scheme Int64 where
  toScheme x = IntegerVal (cast x)

  fromScheme (IntegerVal x) = Just (cast x)
  fromScheme _ = Nothing

export
Scheme Bits8 where
  toScheme x = IntegerVal (cast x)

  fromScheme (IntegerVal x) = Just (cast x)
  fromScheme _ = Nothing

export
Scheme Bits16 where
  toScheme x = IntegerVal (cast x)

  fromScheme (IntegerVal x) = Just (cast x)
  fromScheme _ = Nothing

export
Scheme Bits32 where
  toScheme x = IntegerVal (cast x)

  fromScheme (IntegerVal x) = Just (cast x)
  fromScheme _ = Nothing

export
Scheme Bits64 where
  toScheme x = IntegerVal (cast x)

  fromScheme (IntegerVal x) = Just (cast x)
  fromScheme _ = Nothing

export
Scheme String where
  toScheme x = StringVal x

  fromScheme (StringVal x) = Just x
  fromScheme _ = Nothing

export
Scheme Double where
  toScheme x = FloatVal x

  fromScheme (FloatVal x) = Just x
  fromScheme _ = Nothing

export
Scheme Char where
  toScheme x = CharVal x

  fromScheme (CharVal x) = Just x
  fromScheme _ = Nothing

export
Scheme Bool where
  toScheme False = IntegerVal 0
  toScheme True = IntegerVal 1

  fromScheme (IntegerVal 0) = Just False
  fromScheme (IntegerVal 1) = Just True
  fromScheme _ = Nothing

export
Scheme a => Scheme (List a) where
  toScheme [] = Null
  toScheme (x :: xs) = Cons (toScheme x) (toScheme xs)

  fromScheme Null = Just []
  fromScheme (Cons x xs) = Just $ !(fromScheme x) :: !(fromScheme xs)
  fromScheme _ = Nothing

export
(Scheme a, Scheme b) => Scheme (a, b) where
  toScheme (x, y) = Cons (toScheme x) (toScheme y)
  fromScheme (Cons x y) = Just (!(fromScheme x), !(fromScheme y))
  fromScheme _ = Nothing

export
Scheme a => Scheme (Maybe a) where
  toScheme Nothing = Null
  toScheme (Just x) = Box (toScheme x)

  fromScheme Null = Just Nothing
  fromScheme (Box x) = Just $ Just !(fromScheme x)
  fromScheme _ = Nothing

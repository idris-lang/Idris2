module Compiler.ES.Codegen

import Compiler.Common
import Core.CompileExpr
import Core.Context
import Core.Context.Log
import Core.Directory
import Core.Options
import Core.Env
import Core.Normalise
import Data.List1
import Data.String
import Compiler.ES.Ast
import Compiler.ES.Doc
import Compiler.ES.ToAst
import Compiler.ES.TailRec
import Compiler.ES.State
import Compiler.NoMangle
import Libraries.Data.SortedMap
import Protocol.Hex
import Libraries.Data.String.Extra

import Idris.Pretty.Annotations
import Idris.Syntax
import Idris.Doc.String

import Data.Vect

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

-- Split at the given character and remove it.
breakDrop1 : Char -> String -> (String, String)
breakDrop1 c = mapSnd (drop 1) . break (== c)

-- Display a quoted list of strings.
stringList : List String -> String
stringList = fastConcat . intersperse "," . map show

--------------------------------------------------------------------------------
--          JS Strings
--------------------------------------------------------------------------------

-- Convert an Idris2 string to a Javascript String
-- by escaping most non-alphanumeric characters.
jsString : String -> String
jsString s = "'" ++ (concatMap okchar (unpack s)) ++ "'"
  where
    okchar : Char -> String
    okchar c = if (c >= ' ') && (c /= '\\')
                  && (c /= '"') && (c /= '\'') && (c <= '~')
                  then cast c
                  else case c of
                            '\0' => "\\0"
                            '\'' => "\\'"
                            '"' => "\\\""
                            '\r' => "\\r"
                            '\n' => "\\n"
                            other => "\\u{" ++ asHex (cast c) ++ "}"

||| Alias for Text . jsString
jsStringDoc : String -> Doc
jsStringDoc = Text . jsString

-- A name from the preamble (file `support.js`).
-- the given string is just prefixed with an underscore.
esName : String -> String
esName x = "_" ++ x

-- convert a string to a Javascript identifier
-- by escaping non-alphanumeric characters (except underscores).
jsIdent : String -> String
jsIdent s = concatMap okchar (unpack s)
  where
    okchar : Char -> String
    okchar '_' = "_"
    okchar c = if isAlphaNum c
                  then cast c
                  else "x" ++ asHex (cast c)

jsReservedNames : List String
jsReservedNames =
  [ "await", "break", "case", "catch", "class", "const", "continue", "debugger"
  , "default", "delete", "do", "else", "enum", "export", "extends", "false"
  , "finally", "for", "function", "if", "implements", "import", "in"
  , "instanceof", "interface", "let", "new", "null", "package", "private"
  , "protected", "public", "return", "static", "super", "switch", "this"
  , "throw", "true", "try", "typeof", "var", "void", "while", "with", "yield"
  ]

keywordSafe : String -> String
keywordSafe s = if s `elem` jsReservedNames
  then s ++ "$"
  else s

--------------------------------------------------------------------------------
--          JS Name
--------------------------------------------------------------------------------

jsUserName : UserName -> String
jsUserName (Basic n) = keywordSafe $ jsIdent n
jsUserName (Field n) = "rf__" ++ jsIdent n
jsUserName Underscore = keywordSafe $ jsIdent "_"

jsMangleName : Name -> String
jsMangleName (NS ns n) = jsIdent (showNSWithSep "_" ns) ++ "_" ++ jsMangleName n
jsMangleName (UN n) = jsUserName n
jsMangleName (MN n i) = jsIdent n ++ "_" ++ show i
jsMangleName (PV n d) = "pat__" ++ jsMangleName n
jsMangleName (DN _ n) = jsMangleName n
jsMangleName (Nested (i, x) n) = "n__" ++ show i ++ "_" ++ show x ++ "_" ++ jsMangleName n
jsMangleName (CaseBlock x y) = "case__" ++ jsIdent x ++ "_" ++ show y
jsMangleName (WithBlock x y) = "with__" ++ jsIdent x ++ "_" ++ show y
jsMangleName (Resolved i) = "fn__" ++ show i

parameters (noMangle : NoMangleMap)
  jsName : Name -> String
  jsName n = case isNoMangle noMangle n of
    Just name => name
    Nothing => jsMangleName n

  jsNameDoc : Name -> Doc
  jsNameDoc = Text . jsName

mainExpr : Name
mainExpr = MN "__mainExpression" 0

--------------------------------------------------------------------------------
--          Pretty Printing
--------------------------------------------------------------------------------

parameters (noMangle : NoMangleMap)
  var : Var -> Doc
  var (VName x) = jsNameDoc noMangle x
  var (VLoc x)  = Text $ "$" ++ asHex (cast x)
  var (VRef x)  = Text $ "$R" ++ asHex (cast x)

  minimal : Minimal -> Doc
  minimal (MVar v)          = var v
  minimal (MProjection n v) = minimal v <+> ".a" <+> shown n

tag2es : Tag -> (Doc, Maybe Doc)
tag2es (DataCon i n)  = (shown i, Just (shown (dropNS n)))
tag2es (TypeCon x) = (jsStringDoc $ show x, Nothing)

constant : Doc -> Doc -> Doc
constant n d = "const" <++> n <+> softEq <+> d <+> ";"

applyList : (lparen : Doc) -> (rparen : Doc) -> (sep : Doc) -> List Doc -> Doc
applyList l r sep ds = l <+> (concat $ intersperse sep ds) <+> r

conTags : List Doc -> List Doc
conTags as = zipWith (\i,a => hcat ["a",shown i,softColon,a]) [1..length as] as

applyObj : (args : List Doc) -> Doc
applyObj = applyList "{" "}" softComma

-- fully applied constructors are converted to JS objects with fields
-- labeled `a1`, `a2`, and so on for the given list of arguments.
-- a header field (label: `h`) is added holding either the index of
-- the data constructor used or a string representing the type constructor
-- in question.
--
-- Exceptions based on the given `ConInfo`:
-- `NIL` and `NOTHING`-like data constructors are represented as `{h: 0}`,
-- while `CONS`, `JUST`, and `RECORD` come without the header field.
applyCon : ConInfo -> (tag : Tag) -> (args : List Doc) -> Doc
applyCon NIL     _ [] = "{h" <+> softColon <+> "0}"
applyCon NOTHING _ [] = "{h" <+> softColon <+> "0}"
applyCon CONS    _ as = applyObj (conTags as)
applyCon JUST    _ as = applyObj (conTags as)
applyCon RECORD  _ as = applyObj (conTags as)
applyCon UNIT    _ [] = "undefined"
applyCon _       t as = applyObj (mkCon (tag2es t) :: conTags as)

  where
    mkCon : (Doc, Maybe Doc) -> Doc
    mkCon (t, Nothing) = "h" <+> softColon <+> t
    mkCon (t, Just cmt) = "h" <+> softColon <+> t <++> comment cmt

-- applys the given list of arguments to the given function.
app : (fun : Doc) -> (args : List Doc) -> Doc
app fun args = fun <+> applyList "(" ")" softComma args

-- invoke a function whose name is given as a `String` instead
-- of a `Doc`.
callFun : String -> List Doc -> Doc
callFun = app . Text

-- like `callFun` but with just a single argument
callFun1 : String -> Doc -> Doc
callFun1 fun = callFun fun . pure

-- throws an error in JS land with the given error message.
jsCrashExp : (msg : Doc) -> Doc
jsCrashExp = callFun1 (esName "crashExp")

-- creates a toplevel function definition of the form
-- ```javascript
--  function name(args) {
--    body
--  }
function : (name : Doc) -> (args : List Doc) -> (body : Doc) -> Doc
function n args body =
  "function" <++> app n args <+> SoftSpace <+> block body

--------------------------------------------------------------------------------
--          Primitives
--------------------------------------------------------------------------------

toBigInt : Doc -> Doc
toBigInt = callFun1 "BigInt"

fromBigInt : Doc -> Doc
fromBigInt = callFun1 "Number"

-- we need to use `BigInt` in JS if an integral type's
-- bit size is greater than 32.
useBigInt' : Int -> Bool
useBigInt' = (> 32)

-- same as `useBigInt'` but based on `IntKind`
useBigInt : IntKind -> Bool
useBigInt (Signed $ P x)     = useBigInt' x
useBigInt (Signed Unlimited) = True
useBigInt (Unsigned x)       = useBigInt' x

-- call _bigIntOfString from the preamble, which
-- converts a string to a `BigInt`
jsBigIntOfString : Doc -> Doc
jsBigIntOfString = callFun1 (esName "bigIntOfString")

-- call _parseFloat from the preamble, which
-- converts a string to a `Number`
jsNumberOfString : Doc -> Doc
jsNumberOfString = callFun1 (esName "numberOfString")

-- convert an string to an integral type based
-- on its `IntKind`.
jsIntOfString : IntKind -> Doc -> Doc
jsIntOfString k =
  if useBigInt k
     then jsBigIntOfString
     else callFun1 (esName "intOfString")

-- introduce a binary infix operation
binOp : (symbol : String) -> (lhs : Doc) -> (rhs : Doc) -> Doc
binOp sym lhs rhs = hcat ["(", lhs, Text sym, rhs, ")"]

-- converts a `Number` to an integer
-- based on the given precision (`IntKind`).
toInt : IntKind -> Doc -> Doc
toInt k = if useBigInt k then toBigInt else id

-- converts an integer to a `Number`
-- based on the given precision (`IntKind`).
fromInt : IntKind -> Doc -> Doc
fromInt k = if useBigInt k then fromBigInt else id

-- converts a character (in JS, a string of length 1)
-- to an integer.
jsIntOfChar : IntKind -> Doc -> Doc
jsIntOfChar k s = toInt k $ s <+> ".codePointAt(0)"

-- converts a floating point number to an integer.
jsIntOfDouble : IntKind -> Doc -> Doc
jsIntOfDouble k = toInt k . callFun1 "Math.trunc"

jsAnyToString : Doc -> Doc
jsAnyToString s = "(''+" <+> s <+> ")"

-- converts an integer (`Number` or `BigInt`) to a character
-- by calling `_truncToChar` from the preamble.
jsCharOfInt : IntKind -> Doc -> Doc
jsCharOfInt k = callFun1 (esName "truncToChar") . fromInt k

-- Invokes a function from the preamble to check if an bounded
-- signed integer is within bounds, and - if that's not the case -
-- truncate it accordingly.
-- `isBigInt` reflects whether `int` is a `BigInt` or a `Number`.
--
-- Note: We can't determine `isBigInt` from the given number of bits, since
-- when casting from BigInt (for instance, a `Bits64`) to Number
-- we need to truncate the BigInt
-- first, otherwise we might lose precision.
truncateSigned : (isBigInt : Bool) -> (bits : Int) -> (int : Doc) -> Doc
truncateSigned isBigInt bits =
   let add = if isBigInt then "BigInt" else "Int"
    in callFun1 (esName "trunc" ++ add ++ show bits)

-- like `truncateSigned` but for unsigned integers
truncateUnsigned : (isBigInt : Bool) -> (bits : Int) -> (int : Doc) -> Doc
truncateUnsigned isBigInt bits =
   let add = if isBigInt then "BigInt" else "Int"
    in callFun1 (esName "truncU" ++ add ++ show bits)

integerOp : (op : String) -> (lhs : Doc) -> (rhs : Doc) -> Doc
integerOp op x y = callFun (fastConcat ["_", op, "BigInt"]) [x,y]

-- invokes an arithmetic operation for a bounded integral value.
-- this is used to implement `boundedIntOp` and `boundedUIntOp`
-- where the suffix is set to "s" or "u", respectively.
boundedOp :  (suffix : String)
          -> (bits : Int)
          -> (op : String)
          -> (lhs : Doc)
          -> (rhs : Doc)
          -> Doc
boundedOp s bits o x y = callFun (fastConcat ["_", o, show bits, s]) [x,y]

-- alias for `boundedOp "s"`
boundedIntOp : Int -> String -> Doc -> Doc -> Doc
boundedIntOp = boundedOp "s"

-- alias for `boundedOp "u"`
boundedUIntOp : Int -> String -> Doc -> Doc -> Doc
boundedUIntOp = boundedOp "u"

-- generates code for a boolean binop, like `>=`.
boolOp : (op : String) -> (lhs : Doc) -> (rhs : Doc) -> Doc
boolOp o lhs rhs = "(" <+> binOp o lhs rhs <+> "?1:0)"

jsPrimType : PrimType -> String
jsPrimType _ = "#t"

-- convert an Idris constant to its JS representation
jsConstant : Constant -> String
jsConstant (I i)    = show i
jsConstant (I8 i)   = show i
jsConstant (I16 i)  = show i
jsConstant (I32 i)  = show i
jsConstant (I64 i)  = show i ++ "n"
jsConstant (BI i)   = show i ++ "n"
jsConstant (B8 i)   = show i
jsConstant (B16 i)  = show i
jsConstant (B32 i)  = show i
jsConstant (B64 i)  = show i ++ "n"
jsConstant (Str s)  = jsString s
jsConstant (Ch c)   = jsString $ singleton c
jsConstant (Db f)   = show f
jsConstant (PrT t)  = jsPrimType t
jsConstant WorldVal = esName "idrisworld"

-- Creates the definition of a binary arithmetic operation.
-- Rounding / truncation behavior is determined from the
-- `IntKind`.
arithOp :  Maybe IntKind
        -> (sym : String) -- operator symbol (in case we can use the symbolic version)
        -> (op  : String)  -- operation name (for operations on bounded integrals)
        -> (lhs : Doc)
        -> (rhs : Doc)
        -> Doc
arithOp (Just $ Signed $ P n)     _   op = boundedIntOp n op -- IntXY
arithOp (Just $ Unsigned n)       _   op = boundedUIntOp n op -- BitsXY
arithOp (Just $ Signed Unlimited) ""  op = integerOp op -- Integer
arithOp _                         sym _  = binOp sym

-- use 32bit signed integer for `Int`.
jsIntKind : PrimType -> Maybe IntKind
jsIntKind IntType = Just . Signed $ P 32
jsIntKind x       = intKind x

jsMod : PrimType -> Doc -> Doc -> Doc
jsMod ty x y = case jsIntKind ty of
  (Just $ Signed $ P n) => case useBigInt' n of
    True  => integerOp "mod" x y
    False => callFun "_mod" [x,y]
  (Just $ Unsigned n)   => binOp "%" x y
  _                     => integerOp "mod" x y


-- implementation of all kinds of cast from and / or to integral
-- values.
castInt : PrimType -> PrimType -> Doc -> Core Doc
castInt from to x =
  case ((from, jsIntKind from), (to, jsIntKind to)) of
    ((CharType,_),  (_,Just k)) => truncInt (useBigInt k) k $ jsIntOfChar k x
    ((StringType,_),(_,Just k)) => truncInt (useBigInt k) k (jsIntOfString k x)
    ((DoubleType,_),(_,Just k)) => truncInt (useBigInt k) k $ jsIntOfDouble k x
    ((_,Just k),(CharType,_))   => pure $ jsCharOfInt k x
    ((_,Just k),(StringType,_)) => pure $ jsAnyToString x
    ((_,Just k),(DoubleType,_)) => pure $ fromInt k x
    ((_,Just k1),(_,Just k2))   => intImpl k1 k2
    _ => errorConcat $ ["invalid cast: + ",show from," + ' -> ' + ",show to]
  where
    truncInt : (isBigInt : Bool) -> IntKind -> Doc -> Core Doc
    truncInt b (Signed Unlimited) = pure
    truncInt b (Signed $ P n)     = pure . truncateSigned b n
    truncInt b (Unsigned n)       = pure . truncateUnsigned b n

    shrink : IntKind -> IntKind -> Doc -> Doc
    shrink k1 k2 = case (useBigInt k1, useBigInt k2) of
                        (True, False) => fromBigInt
                        _             => id

    expand : IntKind -> IntKind -> Doc -> Doc
    expand k1 k2 = case (useBigInt k1, useBigInt k2) of
                        (False,True) => toBigInt
                        _            => id

    -- when going from BigInt to Number, we must make
    -- sure to first truncate the BigInt, otherwise we
    -- might get rounding issues
    intImpl : IntKind -> IntKind -> Core Doc
    intImpl k1 k2 =
      let expanded = expand k1 k2 x
          shrunk   = shrink k1 k2 <$> truncInt (useBigInt k1) k2 x
       in case (k1,k2) of
            (_, Signed Unlimited)    => pure $ expanded
            (Signed m, Signed n)     =>
              if n >= m then pure expanded else shrunk

            (Signed _, Unsigned n)   =>
              case (useBigInt k1, useBigInt k2) of
                   (False,True)  => truncInt True k2 (toBigInt x)
                   _             => shrunk

            (Unsigned m, Unsigned n) =>
              if n >= m then pure expanded else shrunk

            -- Only if the precision of the target is greater
            -- than the one of the source, there is no need to cast.
            (Unsigned m, Signed n)   =>
              if n > P m then pure expanded else shrunk

-- implementations of primitive functions.
jsOp : {0 arity : Nat} ->
       PrimFn arity -> Vect arity Doc -> Core Doc
jsOp (Add ty) [x, y] = pure $ arithOp (jsIntKind ty) "+" "add" x y
jsOp (Sub ty) [x, y] = pure $ arithOp (jsIntKind ty) "-" "sub" x y
jsOp (Mul ty) [x, y] = pure $ arithOp (jsIntKind ty) "*" "mul" x y
jsOp (Div DoubleType) [x, y] = pure $ binOp "/" x y
jsOp (Div ty) [x, y] = pure $ arithOp (jsIntKind ty) ""  "div" x y
jsOp (Mod ty) [x, y] = pure $ jsMod ty x y
jsOp (Neg ty) [x] = pure $ "(-(" <+> x <+> "))"
jsOp (ShiftL Int32Type) [x, y] = pure $ binOp "<<" x y
jsOp (ShiftL IntType) [x, y] = pure $ binOp "<<" x y
jsOp (ShiftL ty) [x, y] = pure $ arithOp (jsIntKind ty) "<<" "shl" x y
jsOp (ShiftR Int32Type) [x, y] = pure $ binOp ">>" x y
jsOp (ShiftR IntType) [x, y] = pure $ binOp ">>" x y
jsOp (ShiftR ty) [x, y] = pure $ arithOp (jsIntKind ty) ">>" "shr" x y
jsOp (BAnd Bits32Type) [x, y] = pure $ boundedUIntOp 32 "and" x y
jsOp (BOr Bits32Type) [x, y]  = pure $ boundedUIntOp 32 "or" x y
jsOp (BXOr Bits32Type) [x, y] = pure $ boundedUIntOp 32 "xor" x y
jsOp (BAnd ty) [x, y] = pure $ binOp "&" x y
jsOp (BOr ty) [x, y] = pure $ binOp "|" x y
jsOp (BXOr ty) [x, y] = pure $ binOp "^" x y
jsOp (LT ty) [x, y] = pure $ boolOp "<" x y
jsOp (LTE ty) [x, y] = pure $ boolOp "<=" x y
jsOp (EQ ty) [x, y] = pure $ boolOp "===" x y
jsOp (GTE ty) [x, y] = pure $ boolOp ">=" x y
jsOp (GT ty) [x, y] = pure $ boolOp ">" x y
jsOp StrLength [x] = pure $ x <+> ".length"
jsOp StrHead [x] = pure $ "(" <+> x <+> ".charAt(0))"
jsOp StrTail [x] = pure $ "(" <+> x <+> ".slice(1))"
jsOp StrIndex [x, y] = pure $ "(" <+> x <+> ".charAt(" <+> y <+> "))"
jsOp StrCons [x, y] = pure $ binOp "+" x y
jsOp StrAppend [x, y] = pure $ binOp "+" x y
jsOp StrReverse [x] = pure $ callFun1 (esName "strReverse") x
jsOp StrSubstr [offset, len, str] =
  pure $ callFun (esName "substr") [offset,len,str]
jsOp DoubleExp [x]     = pure $ callFun1 "Math.exp" x
jsOp DoubleLog [x]     = pure $ callFun1 "Math.log" x
jsOp DoublePow [x, y]  = pure $ callFun "Math.pow" [x, y]
jsOp DoubleSin [x]     = pure $ callFun1 "Math.sin" x
jsOp DoubleCos [x]     = pure $ callFun1 "Math.cos" x
jsOp DoubleTan [x]     = pure $ callFun1 "Math.tan" x
jsOp DoubleASin [x]    = pure $ callFun1 "Math.asin" x
jsOp DoubleACos [x]    = pure $ callFun1 "Math.acos" x
jsOp DoubleATan [x]    = pure $ callFun1 "Math.atan" x
jsOp DoubleSqrt [x]    = pure $ callFun1 "Math.sqrt" x
jsOp DoubleFloor [x]   = pure $ callFun1 "Math.floor" x
jsOp DoubleCeiling [x] = pure $ callFun1 "Math.ceil" x

jsOp (Cast StringType DoubleType) [x] = pure $ jsNumberOfString x
jsOp (Cast ty StringType) [x] = pure $ jsAnyToString x
jsOp (Cast ty ty2) [x]        = castInt ty ty2 x
jsOp BelieveMe [_,_,x] = pure x
jsOp (Crash) [_, msg] = pure $ jsCrashExp msg

--------------------------------------------------------------------------------
--          FFI
--------------------------------------------------------------------------------

-- from an FFI declaration, reads the backend to use.
-- Example: `readCCPart "node:lambda: x => x"` yields
-- `("node","lambda: x => x")`.
readCCPart : String -> (String, String)
readCCPart = breakDrop1 ':'

-- search a an FFI implementation for one of the supported
-- backends.
searchForeign : List String -> List String -> Either (List String) String
searchForeign knownBackends decls =
  let pairs = map readCCPart decls
      backends = Left $ map fst pairs
   in maybe backends (Right. snd) $ find ((`elem` knownBackends) . fst) pairs

-- given a function name and FFI implementation string,
-- generate a toplevel function definition.
makeForeign :  {auto d : Ref Ctxt Defs}
            -> {auto c : Ref ESs ESSt}
            -> {auto nm : Ref NoMangleMap NoMangleMap}
            -> (name : Name)
            -> (ffDecl : String)
            -> Core Doc
makeForeign n x = do
  nd <- var !(get NoMangleMap) <$> getOrRegisterRef n
  let (ty, def) = readCCPart x
  case ty of
    "lambda" => pure . constant nd . paren $ Text def
    "support" => do
      let (name, lib) = breakDrop1 ',' def
      lib_code <- readDataFile ("js/" ++ lib ++ ".js")
      addToPreamble lib lib_code
      pure . constant nd . Text $ lib ++ "_" ++ name
    "stringIterator" =>
      case def of
        "new"      => pure $ constant nd "__prim_stringIteratorNew"
        "next"     => pure $ constant nd "__prim_stringIteratorNext"
        "toString" => pure $ constant nd "__prim_stringIteratorToString"
        _ => errorConcat
               [ "Invalid string iterator function: ", def, ". "
               , "Supported functions are: "
               , stringList ["new","next","toString"], "."
               ]

    _ => errorConcat
           [ "Invalid foreign type : ", ty, ". "
           , "Supported types are: "
           , stringList ["lambda", "support", "stringIterator"]
           ]

-- given a function name and list of FFI declarations, tries
-- to extract a declaration for one of the supported backends.
foreignDecl :  {auto d : Ref Ctxt Defs}
            -> {auto c : Ref ESs ESSt}
            -> {auto nm : Ref NoMangleMap NoMangleMap}
            -> Name
            -> List String
            -> Core Doc
foreignDecl n ccs = do
  tys <- ccTypes <$> get ESs
  case searchForeign tys ccs of
    Right x        => makeForeign n x
    Left  backends =>
      errorConcat
        [ "No supported backend found in the definition of ", show n, ". "
        , "Supported backends: ", stringList tys, ". "
        , "Backends in definition: ", stringList backends, "."
        ]

-- implementations for external primitive functions.
jsPrim : {auto c : Ref ESs ESSt} -> Name -> List Doc -> Core Doc
jsPrim nm docs = case (dropAllNS nm, docs) of
  (UN (Basic "prim__newIORef"), [_,v,_]) => pure $ hcat ["({value:", v, "})"]
  (UN (Basic "prim__readIORef"), [_,r,_]) => pure $ hcat ["(", r, ".value)"]
  (UN (Basic "prim__writeIORef"), [_,r,v,_]) => pure $ hcat ["(", r, ".value=", v, ")"]
  (UN (Basic "prim__newArray"), [_,s,v,_]) => pure $ hcat ["(Array(", s, ").fill(", v, "))"]
  (UN (Basic "prim__arrayGet"), [_,x,p,_]) => pure $ hcat ["(", x, "[", p, "])"]
  (UN (Basic "prim__arraySet"), [_,x,p,v,_]) => pure $ hcat ["(", x, "[", p, "]=", v, ")"]
  (UN (Basic "void"), [_, _]) => pure . jsCrashExp $ jsStringDoc "Error: Executed 'void'"
  (UN (Basic "prim__void"), [_, _]) => pure . jsCrashExp $ jsStringDoc "Error: Executed 'void'"
  (UN (Basic "prim__codegen"), []) => do
    (cg :: _) <- ccTypes <$> get ESs
        | _ => pure "\"javascript\""
    pure . Text $ jsString cg

-- fix #1839: Only support `prim__os` in Node backend but not in browsers
  (UN (Basic "prim__os"), []) => do
    tys <- ccTypes <$> get ESs
    case searchForeign tys ["node"] of
      Right _ => do
        addToPreamble "prim__os" $
          "const _sysos = ((o => o === 'linux'?'unix':o==='win32'?'windows':o)" ++
          "(require('os').platform()));"
        pure $ Text $ esName "sysos"
      Left  _ =>
        throw $ InternalError $ "prim not implemented: prim__os"

  _ => throw $ InternalError $ "prim not implemented: " ++ show nm

--------------------------------------------------------------------------------
--          Codegen
--------------------------------------------------------------------------------

-- checks, whether we accept the given `Exp` as a function argument, or
-- whether it needs to be lifted to the surrounding scope and assigned
-- to a new variable.
isArg : CGMode -> Exp -> Bool
isArg Pretty (ELam _ $ Block _ _)           = False
isArg Pretty (ELam _ $ ConSwitch _ _ _ _)   = False
isArg Pretty (ELam _ $ ConstSwitch _ _ _ _) = False
isArg Pretty (ELam _ $ Error _)             = False
isArg _      _                              = True

-- like `isArg` but for function expressions, which we are about
-- to apply
isFun : Exp -> Bool
isFun (ELam _ _) = False
isFun _          = True

-- creates a JS switch statment from the given scrutinee and
-- case blocks (the first entry in a pair is the value belonging
-- to a `case` statement, the second is the body
--
-- Example: switch "foo.a1" [(("0", Just "True"),"return 2;")] (Just "return 0;")
-- generates the following code:
-- ```javascript
--   switch(foo.a1) {
--     case 0: /* True */ return 2;
--     default: return 0;
--   }
-- ```
switch :  (scrutinee : Doc)
       -> (alts : List ((Doc,Maybe Doc),Doc)) -- match, comment, code
       -> (def : Maybe Doc)
       -> Doc
switch sc alts def =
  let stmt    = "switch" <+> paren sc <+> SoftSpace
      defcase = concatMap (pure . anyCase "default" Nothing) def
   in stmt <+> block (vcat $ map alt alts ++ defcase)

  where anyCase : Doc -> Maybe Doc -> Doc -> Doc
        anyCase s cmt d =
          let b = if isMultiline d then block d else d in
          case cmt of
            Nothing => s <+> softColon <+> b
            Just cmt => s <+> softColon <+> comment cmt <++> b

        alt : ((Doc,Maybe Doc),Doc) -> Doc
        alt ((e, c), d) = anyCase ("case" <++> e) c d

-- creates an argument list for a (possibly multi-argument)
-- anonymous function. An empty argument list is treated
-- as a delayed computation (prefixed by `() =>`).
lambdaArgs : (noMangle : NoMangleMap) -> List Var -> Doc
lambdaArgs noMangle [] = "()" <+> lambdaArrow
lambdaArgs noMangle xs = hcat $ (<+> lambdaArrow) . var noMangle <$> xs

insertBreak : (r : Effect) -> (a, Doc) -> (a, Doc)
insertBreak Returns x = x
insertBreak (ErrorWithout _) (pat, exp) = (pat, vcat [exp, "break;"])

mutual
  -- converts an `Exp` to JS code
  exp :  {auto c : Ref ESs ESSt}
      -> {auto nm : Ref NoMangleMap NoMangleMap}
      -> Exp
      -> Core Doc
  exp (EMinimal x) = pure $ minimal !(get NoMangleMap) x
  exp (ELam xs (Return $ y@(ECon _ _ _))) = do
     nm <- get NoMangleMap
     map (\e => lambdaArgs nm xs <+> paren e) (exp y)
  exp (ELam xs (Return $ y)) = do
     nm <- get NoMangleMap
     (lambdaArgs nm xs <+> ) <$> exp y
  exp (ELam xs y) = do
     nm <- get NoMangleMap
     (lambdaArgs nm xs <+>) . block <$> stmt y
  exp (EApp x xs) = do
    o    <- exp x
    args <- traverse exp xs
    pure $ app o args

  exp (ECon tag ci xs) = applyCon ci tag <$> traverse exp xs

  exp (EOp x xs) = traverseVect exp xs >>= jsOp x
  exp (EExtPrim x xs) = traverse exp xs >>= jsPrim x
  exp (EPrimVal x) = pure . Text $ jsConstant x
  exp EErased = pure "undefined"

  -- converts a `Stmt e` to JS code.
  stmt :  {e : _}
       -> {auto c : Ref ESs ESSt}
       -> {auto nm : Ref NoMangleMap NoMangleMap}
       -> Stmt e
       -> Core Doc
  stmt (Return y) = (\e => "return" <++> e <+> ";") <$> exp y
  stmt (Const v x) = do
    nm <- get NoMangleMap
    constant (var nm v) <$> exp x
  stmt (Declare v s) = do
    nm <- get NoMangleMap
    (\d => vcat ["let" <++> var nm v <+> ";",d]) <$> stmt s
  stmt (Assign v x) = do
    nm <- get NoMangleMap
    (\d => hcat [var nm v,softEq,d,";"]) <$> exp x

  stmt (ConSwitch r sc alts def) = do
    as <- traverse (map (insertBreak r) . alt) alts
    d  <- traverseOpt stmt def
    nm <- get NoMangleMap
    pure $ switch (minimal nm sc <+> ".h") as d
    where
        alt : {r : _} -> EConAlt r -> Core ((Doc,Maybe Doc),Doc)
        alt (MkEConAlt _ RECORD b)  = (("undefined",Just "record"),) <$> stmt b
        alt (MkEConAlt _ NIL b)     = (("0",Just "nil"),) <$> stmt b
        alt (MkEConAlt _ CONS b)    = (("undefined",Just "cons"),) <$> stmt b
        alt (MkEConAlt _ NOTHING b) = (("0",Just "nothing"),) <$> stmt b
        alt (MkEConAlt _ JUST b)    = (("undefined",Just "just"),) <$> stmt b
        alt (MkEConAlt _ UNIT b)    = (("undefined",Just "unit"),) <$> stmt b
        alt (MkEConAlt t _ b)       = (tag2es t,) <$> stmt b

  stmt (ConstSwitch r sc alts def) = do
    as <- traverse (map (insertBreak r) . alt) alts
    d  <- traverseOpt stmt def
    ex <- exp sc
    pure $ switch ex as d
    where
        alt : EConstAlt r -> Core ((Doc,Maybe Doc),Doc)
        alt (MkEConstAlt c b) = do
            d <- stmt b
            pure ((Text $ jsConstant c, Nothing), d)

  stmt (Error x)   = pure $ jsCrashExp (jsStringDoc x) <+> ";"
  stmt (Block ss s) = do
    docs <- traverse stmt $ forget ss
    doc  <- stmt s
    pure $ vcat (docs ++ [doc])

-- pretty print a piece of code based on the given
-- codegen mode.
printDoc : CGMode -> Doc -> String
printDoc Pretty y = pretty (y <+> LineBreak)
printDoc Compact y = compact y
printDoc Minimal y = compact y

-- generate code for the given toplevel function.
def :  {auto c : Ref Ctxt Defs}
    -> {auto s : Ref Syn SyntaxInfo}
    -> {auto e : Ref ESs ESSt}
    -> {auto nm : Ref NoMangleMap NoMangleMap}
    -> Function
    -> Core String
def (MkFunction n as body) = do
  reset
  defs <- get Ctxt
  mty <- do log "compiler.javascript.doc" 50 $ "Looking up \{show n}"
            Just gdef <- lookupCtxtExact n (gamma defs)
              | Nothing => pure Nothing
            let UN _ = dropNS n
              | _ => pure Nothing
            ty <- prettyType (const ()) gdef.type
            pure (Just (shown ty))
  ref  <- getOrRegisterRef n
  args <- traverse registerLocal as
  mde  <- mode <$> get ESs
  b    <- stmt Returns body >>= stmt
  let cmt = comment $ hsep (shown n :: toList ((":" <++>) <$> mty))
  case args of
    -- zero argument toplevel functions are converted to
    -- lazily evaluated constants.
    [] => pure $ printDoc mde $ vcat
          [ cmt
          , constant (var !(get NoMangleMap) ref)
               ("__lazy(" <+> function neutral [] b <+> ")") ]
    _  => pure $ printDoc mde $ vcat
          [ cmt
          , function (var !(get NoMangleMap) ref)
               (map (var !(get NoMangleMap)) args) b ]

-- generate code for the given foreign function definition
foreign :  {auto c : Ref ESs ESSt}
        -> {auto d : Ref Ctxt Defs}
        -> {auto nm : Ref NoMangleMap NoMangleMap}
        -> (Name,FC,NamedDef)
        -> Core (List String)
foreign (n, _, MkNmForeign path _ _) = pure . pretty <$> foreignDecl n path
foreign _                            = pure []

-- name of the toplevel tail call loop from the
-- preamble.
tailRec : Name
tailRec = UN $ Basic "__tailRec"

validJSName : String -> Bool
validJSName name =
    not (name `elem` jsReservedNames)
    && all validNameChar (unpack name)
    && (case strM name of
      StrNil => True
      StrCons head _ => not $ isDigit head)
  where
    validNameChar : Char -> Bool
    validNameChar c = isAlphaNum c || c == '_' || c == '$'

||| Compiles the given `ClosedTerm` for the list of supported
||| backends to JS code.
export
compileToES : Ref Ctxt Defs -> Ref Syn SyntaxInfo ->
              (cg : CG) -> ClosedTerm -> List String -> Core String
compileToES c s cg tm ccTypes = do
  _ <- initNoMangle ccTypes validJSName

  cdata <- getCompileDataWith ccTypes False Cases tm

  -- read a derive the codegen mode to use from
  -- user defined directives for the
  directives <- getDirectives cg
  let mode = if "minimal" `elem` directives then Minimal
             else if "compact" `elem` directives then Compact
             else Pretty

  -- initialize the state used in the code generator
  s <- newRef ESs $ init mode (isArg mode) isFun ccTypes !(get NoMangleMap)

  -- register the toplevel `__tailRec` function to make sure
  -- it is not mangled in `Minimal` mode
  addRef tailRec (VName tailRec)

  -- the list of all toplevel definitions (including the main
  -- function)
  let allDefs =  (mainExpr, EmptyFC, MkNmFun [] $ forget cdata.mainExpr)
              :: cdata.namedDefs

      -- tail-call optimized set of toplevel functions
      defs    = TailRec.functions tailRec allDefs

  -- pretty printed toplevel function definitions
  defDecls <- traverse def defs

  -- pretty printed toplevel FFI definitions
  foreigns <- concat <$> traverse foreign allDefs

  -- lookup the (possibly mangled) name of the main function
  mainName <- compact . var !(get NoMangleMap) <$> getOrRegisterRef mainExpr

  -- main function and list of all declarations
  let main =  "try{"
           ++ mainName
           ++ "()}catch(e){if(e instanceof IdrisError){console.log('ERROR: ' + e.message)}else{throw e} }"

      allDecls = fastUnlines $ foreigns ++ defDecls

  st <- get ESs

  -- main preamble containing primops implementations
  static_preamble <- readDataFile ("js/support.js")

  -- complete preamble, including content from additional
  -- support files (if any)
  let pre = showSep "\n" $ static_preamble :: (values $ preamble st)

  pure $ fastUnlines [pre,allDecls,main]

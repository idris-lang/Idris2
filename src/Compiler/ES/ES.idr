module Compiler.ES.ES

import Compiler.Common
import Compiler.ES.Imperative
import Libraries.Utils.Hex
import Data.List1
import Data.Strings
import Libraries.Data.SortedMap
import Libraries.Data.String.Extra

import Core.Directory

%hide Data.Strings.lines
%hide Data.Strings.lines'
%hide Data.Strings.unlines
%hide Data.Strings.unlines'

data ESs : Type where

record ESSt where
  constructor MkESSt
  preamble : SortedMap String String
  ccTypes : List String


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
                            other => "\\u{" ++ asHex (cast {to=Int} c) ++ "}"

esName : String -> String
esName x = "__esPrim_" ++ x


addToPreamble : {auto c : Ref ESs ESSt} ->
                String -> String -> String -> Core String
addToPreamble name newName def =
  do
    s <- get ESs
    case lookup name (preamble s) of
      Nothing =>
        do
          put ESs (record { preamble = insert name def (preamble s) } s)
          pure newName
      Just x =>
        if x /= def
         then throw $ InternalError $ "two incompatible definitions for "
                         ++ name ++ "<|" ++ x ++"|> <|"++ def ++ "|>"
         else pure newName

addConstToPreamble : {auto c : Ref ESs ESSt} -> String -> String -> Core String
addConstToPreamble name def =
  do
    let newName = esName name
    let v = "const " ++ newName ++ " = (" ++ def ++ ");"
    addToPreamble name newName v

addSupportToPreamble : {auto c : Ref ESs ESSt} -> String -> String -> Core String
addSupportToPreamble name code =
  addToPreamble name name code

addStringIteratorToPreamble : {auto c : Ref ESs ESSt} -> Core String
addStringIteratorToPreamble =
  do
    let defs = unlines $
      [ "function __prim_stringIteratorNew(str) {"
      , "  return 0;"
      , "}"
      , "function __prim_stringIteratorToString(_, str, it, f) {"
      , "  return f(str.slice(it));"
      , "}"
      , "function __prim_stringIteratorNext(str, it) {"
      , "  if (it >= str.length)"
      , "    return {h: 0};"
      , "  else"
      , "    return {h: 1, a1: str.charAt(it), a2: it + 1};"
      , "}"
      ]
    let name = "stringIterator"
    let newName = esName name
    addToPreamble name newName defs

jsIdent : String -> String
jsIdent s = concatMap okchar (unpack s)
  where
    okchar : Char -> String
    okchar c = if isAlphaNum c
                  then cast c
                  else "$" ++ the (String) (asHex (cast {to=Int} c))

keywordSafe : String -> String
keywordSafe "var" = "var_"
keywordSafe s = s

jsName : Name -> String
jsName (NS ns n) = jsIdent (showNSWithSep "_" ns) ++ "_" ++ jsName n
jsName (UN n) = keywordSafe $ jsIdent n
jsName (MN n i) = jsIdent n ++ "_" ++ show i
jsName (PV n d) = "pat__" ++ jsName n
jsName (DN _ n) = jsName n
jsName (RF n) = "rf__" ++ jsIdent n
jsName (Nested (i, x) n) = "n__" ++ show i ++ "_" ++ show x ++ "_" ++ jsName n
jsName (CaseBlock x y) = "case__" ++ jsIdent x ++ "_" ++ show y
jsName (WithBlock x y) = "with__" ++ jsIdent x ++ "_" ++ show y
jsName (Resolved i) = "fn__" ++ show i

jsCrashExp : {auto c : Ref ESs ESSt} -> String -> Core String
jsCrashExp message  =
  do
    n <- addConstToPreamble "crashExp" "x=>{throw new IdrisError(x)}"
    pure $ n ++ "("++ message ++ ")"

jsIntegerOfString : {auto c : Ref ESs ESSt} -> String -> Core String
jsIntegerOfString x =
  do
    n <- addConstToPreamble "integerOfString" "s=>{const idx = s.indexOf('.'); return idx === -1 ? BigInt(s) : BigInt(s.slice(0, idx));}"
    pure $ n ++ "(" ++ x ++ ")"

nSpaces : Nat -> String
nSpaces n = pack $ List.replicate n ' '

binOp : String -> String -> String -> String
binOp o lhs rhs = "(" ++ lhs ++ " " ++ o ++ " " ++ rhs ++ ")"

toBigInt : String -> String
toBigInt e = "BigInt(" ++ e ++ ")"

fromBigInt : String -> String
fromBigInt e = "Number(" ++ e ++ ")"

jsIntegerOfChar : String -> String
jsIntegerOfChar s = toBigInt (s++ ".codePointAt(0)")

jsIntegerOfDouble : String -> String
jsIntegerOfDouble s = toBigInt $ "Math.trunc(" ++ s ++ ")"

jsAnyToString : String -> String
jsAnyToString s = "(''+" ++ s ++ ")"


makeIntBound : {auto c : Ref ESs ESSt} -> Int -> Core String
makeIntBound bits = addConstToPreamble ("int_bound_" ++ show bits) ("BigInt(2) ** BigInt("++ show bits ++") ")

truncateInt : {auto c : Ref ESs ESSt} -> Int -> String -> Core String
truncateInt bits e =
  let bs = show bits
   in do
         mn <- addConstToPreamble ("int_mask_neg_" ++ bs)
                                  ("BigInt(-1) << BigInt(" ++ bs ++")")
         mp <- addConstToPreamble ("int_mask_pos_" ++ bs)
                                  ("(BigInt(1) << BigInt(" ++ bs ++")) - BigInt(1)")
         pure $ concat {t = List}
                       [ "((", mn, " & ", e, ") == BigInt(0) ? "
                       , "(", e, " & ", mp, ") : "
                       , "(", e, " | ", mn, ")"
                       , ")"
                       ]

-- Valid unicode code poing range is [0,1114111], therefore,
-- we calculate the remainder modulo 1114112 (= 17 * 2^16).
truncChar : {auto c : Ref ESs ESSt} -> String -> Core String
truncChar e =
  do fn <- addConstToPreamble ("truncToChar") ("x=>(x >= 0 && x <= 55295) || (x >= 57344 && x <= 1114111) ? x : 0")
     pure $ "String.fromCodePoint(" ++ fn ++ "(" ++ fromBigInt e ++ "))"

boundedInt : {auto c : Ref ESs ESSt} -> Int -> String -> Core String
boundedInt bits e =
  do
    n  <- makeIntBound bits
    fn <- addConstToPreamble ("truncToInt"++show bits) ("x=>(x<(-" ++ n ++ ")||(x>=" ++ n ++ "))?x%" ++ n ++ ":x")
    pure $ fn ++ "(" ++ e ++ ")"

boundedUInt : {auto c : Ref ESs ESSt} -> Int -> String -> Core String
boundedUInt bits e =
  do
    n  <- makeIntBound bits
    fn <- addConstToPreamble ("truncToUInt"++show bits) ("x=>{const m = x%" ++ n ++ ";return m>=0?m:m+" ++ n ++ "}")
    pure $ fn ++ "(" ++ e ++ ")"

boundedIntOp : {auto c : Ref ESs ESSt} -> Int -> String -> String -> String -> Core String
boundedIntOp bits o lhs rhs = boundedInt bits (binOp o lhs rhs)

boundedIntBitOp : {auto c : Ref ESs ESSt} -> Int -> String -> String -> String -> Core String
boundedIntBitOp bits o lhs rhs = truncateInt bits (binOp o lhs rhs)

boundedUIntOp : {auto c : Ref ESs ESSt} -> Int -> String -> String -> String -> Core String
boundedUIntOp bits o lhs rhs = boundedUInt bits (binOp o lhs rhs)

boolOp : String -> String -> String -> String
boolOp o lhs rhs = "(" ++ binOp o lhs rhs ++ " ? BigInt(1) : BigInt(0))"

jsConstant : {auto c : Ref ESs ESSt} -> Constant -> Core String
jsConstant (I i) = pure $ show i ++ "n"
jsConstant (I8 i) = pure $ show i ++ "n"
jsConstant (I16 i) = pure $ show i ++ "n"
jsConstant (I32 i) = pure $ show i ++ "n"
jsConstant (I64 i) = pure $ show i ++ "n"
jsConstant (BI i) = pure $ show i ++ "n"
jsConstant (Str s) = pure $ jsString s
jsConstant (Ch c) = pure $ jsString $ Data.Strings.singleton c
jsConstant (Db f) = pure $ show f
jsConstant WorldVal = addConstToPreamble "idrisworld" "Symbol('idrisworld')";
jsConstant (B8 i) = pure $ show i ++ "n"
jsConstant (B16 i) = pure $ show i ++ "n"
jsConstant (B32 i) = pure $ show i ++ "n"
jsConstant (B64 i) = pure $ show i ++ "n"
jsConstant ty = throw (InternalError $ "Unsuported constant " ++ show ty)

-- Creates the definition of a binary arithmetic operation.
-- Rounding / truncation behavior is determined from the
-- `IntKind`.
arithOp :  {auto c : Ref ESs ESSt}
        -> Maybe IntKind
        -> (op : String)
        -> (x : String)
        -> (y : String)
        -> Core String
arithOp (Just $ Signed $ P n) op x y = boundedIntOp (n-1) op x y
arithOp (Just $ Unsigned n)   op x y = boundedUIntOp n op x y
arithOp _                     op x y = pure $ binOp op x y

-- Same as `arithOp` but for bitwise operations that might
-- go out of the valid range.
bitOp :  {auto c : Ref ESs ESSt}
      -> Maybe IntKind
      -> (op : String)
      -> (x : String)
      -> (y : String)
      -> Core String
bitOp (Just $ Signed $ P n) op x y = boundedIntBitOp (n-1) op x y
bitOp (Just $ Unsigned n)   op x y = boundedUIntOp n op x y
bitOp _                     op x y = pure $ binOp op x y

constPrimitives : {auto c : Ref ESs ESSt} -> ConstantPrimitives
constPrimitives = MkConstantPrimitives {
    charToInt    = \k => truncInt k . jsIntegerOfChar
  , intToChar    = \_ => truncChar
  , stringToInt  = \k,s => jsIntegerOfString s >>= truncInt k
  , intToString  = \_   => pure . jsAnyToString
  , doubleToInt  = \k => truncInt k . jsIntegerOfDouble
  , intToDouble  = \_ => pure . fromBigInt
  , intToInt     = intImpl
  }
  where truncInt : IntKind -> String -> Core String
        truncInt (Signed Unlimited) = pure
        truncInt (Signed $ P n)     = boundedInt (n-1)
        truncInt (Unsigned n)       = boundedUInt n

        intImpl : IntKind -> IntKind -> String -> Core String
        intImpl _ (Signed Unlimited) = pure
        intImpl (Signed m) k@(Signed n) = if n >= m then pure else truncInt k
        intImpl (Signed _)  k@(Unsigned n) = truncInt k
        intImpl (Unsigned m) k@(Unsigned n) = if n >= m then pure else truncInt k

        -- Only if the precision of the target is greater
        -- than the one of the source, there is no need to cast.
        intImpl (Unsigned m) k@(Signed n) = if n > P m then pure else truncInt k

jsOp : {auto c : Ref ESs ESSt} -> PrimFn arity -> Vect arity String -> Core String
jsOp (Add ty) [x, y] = arithOp (intKind ty) "+" x y
jsOp (Sub ty) [x, y] = arithOp (intKind ty) "-" x y
jsOp (Mul ty) [x, y] = arithOp (intKind ty) "*" x y
jsOp (Div ty) [x, y] = arithOp (intKind ty) "/" x y
jsOp (Mod ty) [x, y] = arithOp (intKind ty) "%" x y
jsOp (Neg ty) [x] = pure $ "(-(" ++ x ++ "))"
jsOp (ShiftL ty) [x, y] = bitOp (intKind ty) "<<" x y
jsOp (ShiftR ty) [x, y] = bitOp (intKind ty) ">>" x y
jsOp (BAnd ty) [x, y] = pure $ binOp "&" x y
jsOp (BOr ty) [x, y] = pure $ binOp "|" x y
jsOp (BXOr ty) [x, y] = pure $ binOp "^" x y
jsOp (LT ty) [x, y] = pure $ boolOp "<" x y
jsOp (LTE ty) [x, y] = pure $ boolOp "<=" x y
jsOp (EQ ty) [x, y] = pure $ boolOp "===" x y
jsOp (GTE ty) [x, y] = pure $ boolOp ">=" x y
jsOp (GT ty) [x, y] = pure $ boolOp ">" x y
jsOp StrLength [x] = pure $ toBigInt $ x ++ ".length"
jsOp StrHead [x] = pure $ "(" ++ x ++ ".charAt(0))"
jsOp StrTail [x] = pure $ "(" ++ x ++ ".slice(1))"
jsOp StrIndex [x, y] = pure $ "(" ++ x ++ ".charAt(" ++ fromBigInt y ++ "))"
jsOp StrCons [x, y] = pure $ binOp "+" x y
jsOp StrAppend [x, y] = pure $ binOp "+" x y
jsOp StrReverse [x] =
  do
    n <- addConstToPreamble "strReverse" "x => x.split('').reverse().join('')"
    pure $ n ++ "(" ++ x ++ ")"
jsOp StrSubstr [offset, length, str] =
  pure $ str ++ ".slice(" ++ fromBigInt offset ++ ", " ++ fromBigInt offset ++ " + " ++ fromBigInt length ++ ")"
jsOp DoubleExp [x] = pure $ "Math.exp(" ++ x ++ ")"
jsOp DoubleLog [x] = pure $ "Math.log(" ++ x ++ ")"
jsOp DoubleSin [x] = pure $ "Math.sin(" ++ x ++ ")"
jsOp DoubleCos [x] = pure $ "Math.cos(" ++ x ++ ")"
jsOp DoubleTan [x] = pure $ "Math.tan(" ++ x ++ ")"
jsOp DoubleASin [x] = pure $ "Math.asin(" ++ x ++ ")"
jsOp DoubleACos [x] = pure $ "Math.acos(" ++ x ++ ")"
jsOp DoubleATan [x] = pure $ "Math.atan(" ++ x ++ ")"
jsOp DoubleSqrt [x] = pure $ "Math.sqrt(" ++ x ++ ")"
jsOp DoubleFloor [x] = pure $ "Math.floor(" ++ x ++ ")"
jsOp DoubleCeiling [x] = pure $ "Math.ceil(" ++ x ++ ")"

jsOp (Cast StringType DoubleType) [x] = pure $ "parseFloat(" ++ x ++ ")"
jsOp (Cast ty StringType) [x] = pure $ jsAnyToString x
jsOp (Cast ty ty2) [x]        = castInt constPrimitives ty ty2 x
jsOp BelieveMe [_,_,x] = pure x
jsOp (Crash) [_, msg] = jsCrashExp msg


readCCPart : String -> (String, String)
readCCPart x =
  let (cc, def) = break (== ':') x
  in (cc, drop 1 def)


searchForeign : List String -> List String -> Maybe String
searchForeign prefixes [] = Nothing
searchForeign prefixes (x::xs) =
  let (cc, def) = readCCPart x
  in if cc `elem` prefixes then Just def
                           else searchForeign prefixes xs


makeForeign : {auto d : Ref Ctxt Defs} -> {auto c : Ref ESs ESSt} -> Name -> String -> Core String
makeForeign n x =
  do
    let (ty, def) = readCCPart x
    case ty of
      "lambda" => pure $ "const " ++ jsName n ++ " = (" ++ def ++ ")\n"
      "support" =>
        do
          let (name, lib_) = break (== ',') def
          let lib = drop 1 lib_
          lib_code <- readDataFile ("js/" ++ lib ++ ".js")
          ignore $ addSupportToPreamble lib lib_code
          pure $ "const " ++ jsName n ++ " = " ++ lib ++ "_" ++ name ++ "\n"
      "stringIterator" =>
        do
          ignore addStringIteratorToPreamble
          case def of
            "new" => pure $ "const " ++ jsName n ++ " = __prim_stringIteratorNew;\n"
            "next" => pure $ "const " ++ jsName n ++ " = __prim_stringIteratorNext;\n"
            "toString" => pure $ "const " ++ jsName n ++ " = __prim_stringIteratorToString;\n"
            _ => throw (InternalError $ "invalid string iterator function: " ++ def ++ ", supported functions are \"new\", \"next\", \"toString\"")


      _ => throw (InternalError $ "invalid foreign type : " ++ ty ++ ", supported types are \"lambda\", \"support\"")

foreignDecl : {auto d : Ref Ctxt Defs} -> {auto c : Ref ESs ESSt} -> Name -> List String -> Core String
foreignDecl n ccs =
  do
    s <- get ESs
    case searchForeign (ccTypes s) ccs of
      Just x => makeForeign n x
      Nothing => throw (InternalError $ "No node or javascript definition found for " ++ show n ++ " in " ++ show ccs)

jsPrim : {auto c : Ref ESs ESSt} -> Name -> List String -> Core String
jsPrim (NS _ (UN "prim__newIORef")) [_,v,_] = pure $ "({value: "++ v ++"})"
jsPrim (NS _ (UN "prim__readIORef")) [_,r,_] = pure $ "(" ++ r ++ ".value)"
jsPrim (NS _ (UN "prim__writeIORef")) [_,r,v,_] = pure $ "(" ++ r ++ ".value=" ++ v ++ ")"
jsPrim (NS _ (UN "prim__newArray")) [_,s,v,_] = pure $ "(Array(Number(" ++ s ++ ")).fill(" ++ v ++ "))"
jsPrim (NS _ (UN "prim__arrayGet")) [_,x,p,_] = pure $ "(" ++ x ++ "[" ++ p ++ "])"
jsPrim (NS _ (UN "prim__arraySet")) [_,x,p,v,_] = pure $ "(" ++ x ++ "[" ++ p ++ "] = " ++ v ++ ")"
jsPrim (NS _ (UN "prim__os")) [] =
  do
    let oscalc = "(o => o === 'linux'?'unix':o==='win32'?'windows':o)"
    sysos <- addConstToPreamble "sysos" (oscalc ++ "(require('os').platform())")
    pure sysos
jsPrim (NS _ (UN "void")) [_, _] = jsCrashExp $ jsString $ "Error: Executed 'void'"  -- DEPRECATED. TODO: remove when bootstrap has been updated
jsPrim (NS _ (UN "prim__void")) [_, _] = jsCrashExp $ jsString $ "Error: Executed 'void'"
jsPrim x args = throw $ InternalError $ "prim not implemented: " ++ (show x)

tag2es : Either Int String -> String
tag2es (Left x) = show x
tag2es (Right x) = jsString x

mutual
  impExp2es : {auto d : Ref Ctxt Defs} -> {auto c : Ref ESs ESSt} -> ImperativeExp -> Core String
  impExp2es (IEVar n) =
    pure $ jsName n
  impExp2es (IELambda args body) =
    pure $ "(" ++ showSep ", " (map jsName args) ++ ") => {" ++ !(imperative2es 0 body) ++ "}"
  impExp2es (IEApp f args) =
    pure $ !(impExp2es f) ++ "(" ++ showSep ", " !(traverse impExp2es args) ++ ")"
  impExp2es (IEConstant c) =
    jsConstant c
  impExp2es (IEPrimFn f args) =
    jsOp f !(traverseVect impExp2es args)
  impExp2es (IEPrimFnExt n args) =
    jsPrim n !(traverse impExp2es args)
  impExp2es (IEConstructorHead e) =
    pure $ !(impExp2es e) ++ ".h"
  impExp2es (IEConstructorTag x) =
    pure $ tag2es x
  impExp2es (IEConstructorArg i e) =
    pure $ !(impExp2es e) ++ ".a" ++ show i
  impExp2es (IEConstructor h args) =
    let argPairs = zipWith (\i,a => "a" ++ show i ++ ": " ++ a ) [1..length args] !(traverse impExp2es args)
    in pure $ "({" ++ showSep ", " (("h:" ++ tag2es h)::argPairs) ++ "})"
  impExp2es (IEDelay e) =
    pure $ "(()=>" ++ !(impExp2es e) ++ ")"
  impExp2es (IEForce e) =
    pure $ !(impExp2es e) ++ "()"
  impExp2es IENull =
    pure "undefined"

  imperative2es : {auto d : Ref Ctxt Defs} -> {auto c : Ref ESs ESSt} -> Nat -> ImperativeStatement -> Core String
  imperative2es indent DoNothing =
    pure ""
  imperative2es indent (SeqStatement x y) =
    pure $ !(imperative2es indent x) ++ "\n" ++ !(imperative2es indent y)
  imperative2es indent (FunDecl fc n args body) =
    pure $ nSpaces indent ++ "function " ++ jsName n ++ "(" ++ showSep ", " (map jsName args) ++ "){//"++ show fc ++"\n" ++
           !(imperative2es (indent+1) body) ++ "\n" ++ nSpaces indent ++ "}\n"
  imperative2es indent (ForeignDecl fc n path args ret) =
    pure $ !(foreignDecl n path) ++ "\n"
  imperative2es indent (ReturnStatement x) =
    pure $ nSpaces indent ++ "return " ++ !(impExp2es x) ++ ";"
  imperative2es indent (SwitchStatement e alts def) =
    do
      def <- case def of
                Nothing => pure ""
                Just x => pure $ nSpaces (indent+1) ++ "default:\n" ++ !(imperative2es (indent+2) x)
      let sw = nSpaces indent ++ "switch(" ++ !(impExp2es e) ++ "){\n"
      let alts = concat !(traverse (alt2es (indent+1)) alts)
      pure $ sw ++ alts ++ def ++ "\n" ++ nSpaces indent ++ "}"
  imperative2es indent (LetDecl x v) =
    case v of
      Nothing => pure $ nSpaces indent ++ "let " ++ jsName x ++ ";"
      Just v_ => pure $ nSpaces indent ++ "let " ++ jsName x ++ " = " ++ !(impExp2es v_) ++ ";"
  imperative2es indent (ConstDecl x v) =
    pure $ nSpaces indent ++ "const " ++ jsName x ++ " = " ++ !(impExp2es v) ++ ";"
  imperative2es indent (MutateStatement x v) =
    pure $ nSpaces indent ++ jsName x ++ " = " ++ !(impExp2es v) ++ ";"
  imperative2es indent (ErrorStatement msg) =
    pure $ nSpaces indent ++ "throw new Error("++ jsString msg ++");"
  imperative2es indent (EvalExpStatement e) =
    pure $ nSpaces indent ++ !(impExp2es e) ++ ";"
  imperative2es indent (CommentStatement x) =
    pure $ "\n/*" ++ x ++ "*/\n"
  imperative2es indent (ForEverLoop x) =
    pure $ nSpaces indent ++ "while(true){\n" ++ !(imperative2es (indent+1) x) ++ "\n" ++ nSpaces indent ++ "}"

  alt2es : {auto d : Ref Ctxt Defs} -> {auto c : Ref ESs ESSt} -> Nat -> (ImperativeExp, ImperativeStatement) -> Core String
  alt2es indent (e, b) = pure $ nSpaces indent ++ "case " ++ !(impExp2es e) ++ ": {\n" ++
                                !(imperative2es (indent+1) b) ++ "\n" ++ nSpaces (indent+1) ++ "break; }\n"

static_preamble : List String
static_preamble =
  [ "class IdrisError extends Error { }"
  , "function __prim_js2idris_array(x){if(x.length ===0){return {h:0}}else{return {h:1,a1:x[0],a2: __prim_js2idris_array(x.slice(1))}}}"
  , "function __prim_idris2js_array(x){const result = Array();while (x.h != 0) {result.push(x.a1); x = x.a2;}return result;}"
  ]

export
compileToES : Ref Ctxt Defs -> ClosedTerm -> List String -> Core String
compileToES c tm ccTypes =
  do
    (impDefs, impMain) <- compileToImperative c tm
    s <- newRef ESs (MkESSt empty ccTypes)
    defs <- imperative2es 0 impDefs
    main_ <- imperative2es 0 impMain
    let main = "try{" ++ main_ ++ "}catch(e){if(e instanceof IdrisError){console.log('ERROR: ' + e.message)}else{throw e} }"
    st <- get ESs
    let pre = showSep "\n" $ static_preamble ++ (SortedMap.values $ preamble st)
    pure $ pre ++ "\n\n" ++ defs ++ main

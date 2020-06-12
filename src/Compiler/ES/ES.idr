module Compiler.ES.ES

import Compiler.ES.Imperative
import Utils.Hex
import Data.Strings
import Data.SortedMap
import Data.String.Extra

data ESs : Type where

record ESSt where
  constructor MkESSt
  preamble : SortedMap String String


esName : String -> String
esName x = "__esPrim_" ++ x

addConstToPreamble : {auto c : Ref ESs ESSt} -> String -> String -> Core String
addConstToPreamble name def =
  do
    s <- get ESs
    let v = "const " ++ esName name ++ " = (" ++ def ++ ")"
    case lookup name (preamble s) of
      Nothing =>
        do
          put ESs (record { preamble = insert name v (preamble s) } s)
          pure $ esName name
      Just x =>
        if x /= v then throw $ InternalError $ "two incompatible definitions for " ++ name ++ "<|" ++ x ++"|> <|"++ v ++ "|>"
                    else pure $ esName name


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
jsName (NS ns n) = showSep "_" (reverse ns) ++ "_" ++ jsName n
jsName (UN n) = keywordSafe $ jsIdent n
jsName (MN n i) = jsIdent n ++ "_" ++ show i
jsName (PV n d) = "pat__" ++ jsName n
jsName (DN _ n) = jsName n
jsName (RF n) = "rf__" ++ jsIdent n
jsName (Nested (i, x) n) = "n__" ++ show i ++ "_" ++ show x ++ "_" ++ jsName n
jsName (CaseBlock x y) = "case__" ++ show x ++ "_" ++ show y
jsName (WithBlock x y) = "with__" ++ show x ++ "_" ++ show y
jsName (Resolved i) = "fn__" ++ show i

jsString : String -> String
jsString s = "'" ++ (concatMap okchar (unpack s)) ++ "'"
  where
    okchar : Char -> String
    okchar c = if (c >= ' ') && (c /= '\\') && (c /= '"') && (c /= '\'') && (c <= '~')
                  then cast c
                  else case c of
                            '\0' => "\\0"
                            '\'' => "\\'"
                            '"' => "\\\""
                            '\r' => "\\r"
                            '\n' => "\\n"
                            other => "\\u{" ++ asHex (cast {to=Int} c) ++ "}"

jsCrashExp : {auto c : Ref ESs ESSt} -> String -> Core String
jsCrashExp message  =
  do
    n <- addConstToPreamble "crashExp" "x=>{throw new Error(x)}"
    pure $ n ++ "("++ jsString message ++ ")"

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

boundedInt : {auto c : Ref ESs ESSt} -> Int -> String -> Core String
boundedInt bits e =
  do
    n <- addConstToPreamble ("int_bound_" ++ show bits) ("BigInt(2) ** BigInt("++ show bits ++") ")
    pure $ "(" ++ e ++ " % " ++ n ++ ")"

boundedIntOp : {auto c : Ref ESs ESSt} -> Int -> String -> String -> String -> Core String
boundedIntOp bits o lhs rhs = boundedInt 63 (binOp o lhs rhs)


boolOp : String -> String -> String -> String
boolOp o lhs rhs = "(" ++ binOp o lhs rhs ++ " ? BigInt(1) : BigInt(0))"

jsConstant : {auto c : Ref ESs ESSt} -> Constant -> Core String
jsConstant (I i) = pure $ toBigInt $ show i
jsConstant (BI i) = pure $ toBigInt $ show i
jsConstant (Str s) = pure $ jsString s
jsConstant (Ch c) = pure $ jsString $ Data.Strings.singleton c
jsConstant (Db f) = pure $ show f
jsConstant WorldVal = addConstToPreamble "idrisworld" "Symbol('idrisworld')";
jsConstant ty = throw (InternalError $ "Unsuported constant " ++ show ty)

jsOp : {auto c : Ref ESs ESSt} -> PrimFn arity -> Vect arity String -> Core String
jsOp (Add IntType) [x, y] = pure $ !(boundedIntOp 63 "+" x y)
jsOp (Sub IntType) [x, y] = pure $ !(boundedIntOp 63 "-" x y)
jsOp (Mul IntType) [x, y] = pure $ !(boundedIntOp 63 "*" x y)
jsOp (Div IntType) [x, y] = pure $ !(boundedIntOp 63 "/" x y)
jsOp (Mod IntType) [x, y] = pure $ !(boundedIntOp 63 "%" x y)
jsOp (Add ty) [x, y] = pure $ binOp "+" x y
jsOp (Sub ty) [x, y] = pure $ binOp "-" x y
jsOp (Mul ty) [x, y] = pure $ binOp "*" x y
jsOp (Div ty) [x, y] = pure $ binOp "/" x y
jsOp (Mod ty) [x, y] = pure $ binOp "%" x y
jsOp (Neg ty) [x] = pure $ "(-(" ++ x ++ "))"
jsOp (ShiftL ty) [x, y] = pure $ binOp "<<" x y
jsOp (ShiftR ty) [x, y] = pure $ binOp ">>" x y
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
jsOp (Cast IntType CharType) [x] = pure $ "String.fromCodePoint(" ++ fromBigInt x ++ ")"
jsOp (Cast IntegerType CharType) [x] = pure $ "String.fromCodePoint(" ++ fromBigInt x ++ ")"
jsOp (Cast CharType IntType) [x] = pure $ toBigInt $ x ++ ".codePointAt(0)"
jsOp (Cast CharType IntegerType) [x] = pure $ toBigInt $ x ++ ".codePointAt(0)"
jsOp (Cast DoubleType IntType) [x] = boundedInt 63 $ "BigInt(Math.floor(" ++ x ++ "))"
jsOp (Cast DoubleType IntegerType) [x] = pure $ "BigInt(Math.floor(" ++ x ++ "))"
jsOp (Cast StringType IntType) [x] = boundedInt 63 $ !(jsIntegerOfString x)
jsOp (Cast StringType IntegerType) [x] = jsIntegerOfString x
jsOp (Cast IntegerType IntType) [x] = boundedInt 63 x
jsOp (Cast IntType IntegerType) [x] = pure x
jsOp (Cast ty DoubleType) [x] = pure $ "parseFloat(" ++ x ++ ")"
jsOp (Cast ty StringType) [x] = pure $ "(''+" ++ x ++ ")"
jsOp (Cast ty ty2) [x] = jsCrashExp $ "invalid cast: + " ++ show ty ++ " + ' -> ' + " ++ show ty2
jsOp BelieveMe [_,_,x] = pure x
jsOp (Crash) [_, msg] = jsCrashExp msg

jsPrim : Name -> List String -> Core String
jsPrim x args = throw (InternalError $ "prim not implemented: " ++ (show x))

searchForeign : List String -> List String -> Maybe String
searchForeign prefixes [] = Nothing
searchForeign prefixes (x::xs) =
  let (cc, def) = break (== ':') x
  in if cc `elem` prefixes then Just $ drop 1 def
                           else searchForeign prefixes xs


makeForeign : Name -> String -> Core String
makeForeign n x =
  do
    let (ty, def) = break (== ',') x
    case ty of
      "lambdaExp" => pure $ "const " ++ jsName n ++ " = (" ++ drop 1 def ++ ")\n"
      _ => throw (InternalError $ "invalid foreign type : " ++ ty ++ ", supporte types are lambdaExp")

foreignDecl : Name -> List String -> Core String
foreignDecl n ccs =
  case searchForeign ["node", "javascript"] ccs of
    Just x => makeForeign n x
    Nothing => throw (InternalError $ "No node or javascript definition found for " ++ show n ++ " in " ++ show ccs)

mutual
  impExp2es : {auto c : Ref ESs ESSt} -> ImperativeExp -> Core String
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
  impExp2es (IEConstructorTag t) =
    pure $ show t
  impExp2es (IEConstructorArg i e) =
    pure $ !(impExp2es e) ++ ".a" ++ show i
  impExp2es (IEConstructor h args) =
    let argPairs = zipWith (\i,a => "a" ++ show i ++ ": " ++ a ) [1..length args] !(traverse impExp2es args)
    in pure $ "({" ++ showSep ", " (("h:" ++ show h)::argPairs) ++ "})"
  impExp2es (IEDelay e) =
    pure $ "(()=>" ++ !(impExp2es e) ++ ")"
  impExp2es (IEForce e) =
    pure $ !(impExp2es e) ++ "()"
  impExp2es IENull =
    pure "undefined"

  imperative2es : {auto c : Ref ESs ESSt} -> Nat -> ImperativeStatement -> Core String
  imperative2es indent DoNothing =
    pure ""
  imperative2es indent (SeqStatement x y) =
    pure $ !(imperative2es indent x) ++ "\n" ++ !(imperative2es indent y)
  imperative2es indent (FunDecl fc n args body) =
    pure $ nSpaces indent ++ "function " ++ jsName n ++ "(" ++ showSep ", " (map jsName args) ++ "){//"++ show fc ++"\n" ++
           !(imperative2es (indent+1) body) ++ "\n" ++ nSpaces indent ++ "}\n"
  imperative2es indent (ForeignDecl n path) =
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

  alt2es : {auto c : Ref ESs ESSt} -> Nat -> (ImperativeExp, ImperativeStatement) -> Core String
  alt2es indent (e, b) = pure $ nSpaces indent ++ "case " ++ !(impExp2es e) ++ ":\n" ++
                                !(imperative2es (indent+1) b) ++ "\n" ++ nSpaces (indent+1) ++ "break;\n"
export
compileToES : Ref Ctxt Defs -> ClosedTerm -> Core String
compileToES c tm =
  do
    statements <- compileToImperative c tm
    s <- newRef ESs (MkESSt empty)
    es_statements <- imperative2es 0 statements
    st <- get ESs
    let pre = showSep "\n" $ SortedMap.values $ preamble st
    pure $ pre ++ "\n\n" ++ es_statements -- ++ "\n\n\n/*" ++ show statements ++ "*/"

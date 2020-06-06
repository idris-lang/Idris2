module Compiler.ES.ES

import Compiler.ES.Imperative
import Utils.Hex
import Data.Strings
import Data.SortedSet

data ESs : Type where

record ESSt where
  constructor MkESSt
  preamble : SortedSet String


addToPreamble : {auto c : Ref ESs ESSt} -> String -> Core ()
addToPreamble new =
  do
    s <- get ESs
    put ESs (record { preamble = insert new (preamble s) } s)
    pure ()

esName : String -> String
esName x = "es_" ++ x

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

nSpaces : Nat -> String
nSpaces n = pack $ List.replicate n ' '

binOp : String -> String -> String -> String
binOp o lhs rhs = "(" ++ lhs ++ " " ++ o ++ " " ++ rhs ++ ")"

toBigInt : String -> String
toBigInt e = "BigInt(" ++ e ++ ")"

fromBigInt : String -> String
fromBigInt e = "Number(" ++ e ++ ")"

boundedInt : Int -> String -> String
boundedInt bits e = "(" ++ e ++ " % __jsPrim_int_bound_" ++ show bits ++ ")"

boundedIntOp : Int -> String -> String -> String -> String
boundedIntOp bits o lhs rhs = boundedInt 63 (binOp o lhs rhs)


boolOp : String -> String -> String -> String
boolOp o lhs rhs = "(" ++ binOp o lhs rhs ++ " ? 1 : 0)"

jsConstant : {auto c : Ref ESs ESSt} -> Constant -> Core String
jsConstant (I i) = pure $ toBigInt $ show i
jsConstant (BI i) = pure $ toBigInt $ show i
jsConstant (Str s) = pure $ jsString s
jsConstant (Ch c) = pure $ jsString $ Data.Strings.singleton c
jsConstant (Db f) = pure $ show f
jsConstant WorldVal =
  do
    let name = esName "idrisworld"
    addToPreamble $ "const " ++ name ++ " = Symbol(\"" ++ name ++ "\")";
    pure name
jsConstant ty = throw (InternalError $ "Unsuported constant " ++ show ty)

jsOp : PrimFn arity -> Vect arity String -> String
jsOp (Add IntType) [x, y] = boundedIntOp 63 "+" x y
jsOp (Sub IntType) [x, y] = boundedIntOp 63 "-" x y
jsOp (Mul IntType) [x, y] = boundedIntOp 63 "*" x y
jsOp (Div IntType) [x, y] = boundedIntOp 63 "/" x y
jsOp (Mod IntType) [x, y] = boundedIntOp 63 "%" x y
jsOp (Add ty) [x, y] = binOp "+" x y
jsOp (Sub ty) [x, y] = binOp "-" x y
jsOp (Mul ty) [x, y] = binOp "*" x y
jsOp (Div ty) [x, y] = binOp "/" x y
jsOp (Mod ty) [x, y] = binOp "%" x y
jsOp (Neg ty) [x] = "(-(" ++ x ++ "))"
jsOp (ShiftL ty) [x, y] = binOp "<<" x y
jsOp (ShiftR ty) [x, y] = binOp ">>" x y
jsOp (BAnd ty) [x, y] = binOp "&" x y
jsOp (BOr ty) [x, y] = binOp "|" x y
jsOp (BXOr ty) [x, y] = binOp "^" x y
jsOp (LT ty) [x, y] = boolOp "<" x y
jsOp (LTE ty) [x, y] = boolOp "<=" x y
jsOp (EQ ty) [x, y] = boolOp "===" x y
jsOp (GTE ty) [x, y] = boolOp ">=" x y
jsOp (GT ty) [x, y] = boolOp ">" x y
jsOp StrLength [x] = toBigInt $ x ++ ".length"
jsOp StrHead [x] = "(" ++ x ++ ".charAt(0))"
jsOp StrTail [x] = "(" ++ x ++ ".slice(1))"
jsOp StrIndex [x, y] = "(" ++ x ++ ".charAt(" ++ fromBigInt y ++ "))"
jsOp StrCons [x, y] = binOp "+" x y
jsOp StrAppend [x, y] = binOp "+" x y
jsOp StrReverse [x] = "__jsPrim_reverseStr(" ++ x ++ ")"
jsOp StrSubstr [offset, length, str] = str ++ ".slice(" ++ fromBigInt offset ++ ", " ++ fromBigInt offset ++ " + " ++ fromBigInt length ++ ")"
jsOp DoubleExp [x] = "Math.exp(" ++ x ++ ")"
jsOp DoubleLog [x] = "Math.log(" ++ x ++ ")"
jsOp DoubleSin [x] = "Math.sin(" ++ x ++ ")"
jsOp DoubleCos [x] = "Math.cos(" ++ x ++ ")"
jsOp DoubleTan [x] = "Math.tan(" ++ x ++ ")"
jsOp DoubleASin [x] = "Math.asin(" ++ x ++ ")"
jsOp DoubleACos [x] = "Math.acos(" ++ x ++ ")"
jsOp DoubleATan [x] = "Math.atan(" ++ x ++ ")"
jsOp DoubleSqrt [x] = "Math.sqrt(" ++ x ++ ")"
jsOp DoubleFloor [x] = "Math.floor(" ++ x ++ ")"
jsOp DoubleCeiling [x] = "Math.ceil(" ++ x ++ ")"
jsOp (Cast IntType CharType) [x] = "String.fromCodePoint(" ++ fromBigInt x ++ ")"
jsOp (Cast IntegerType CharType) [x] = "String.fromCodePoint(" ++ fromBigInt x ++ ")"
jsOp (Cast CharType IntType) [x] = toBigInt $ x ++ ".codePointAt(0)"
jsOp (Cast CharType IntegerType) [x] = toBigInt $ x ++ ".codePointAt(0)"
jsOp (Cast DoubleType IntType) [x] = boundedInt 63 $ "BigInt(Math.floor(" ++ x ++ "))"
jsOp (Cast DoubleType IntegerType) [x] = "BigInt(Math.floor(" ++ x ++ "))"
jsOp (Cast StringType IntType) [x] = boundedInt 63 $ "__jsPrim_integer_of_string(" ++ x ++ ")"
jsOp (Cast StringType IntegerType) [x] = "__jsPrim_integer_of_string(" ++ x ++ ")"
jsOp (Cast IntegerType IntType) [x] = boundedInt 63 x
jsOp (Cast IntType IntegerType) [x] = x
jsOp (Cast ty DoubleType) [x] = "parseFloat(" ++ x ++ ")"
jsOp (Cast ty StringType) [x] = "(''+" ++ x ++ ")" -- this is JavaScript after all
jsOp (Cast ty ty2) [x] = "__jsPrim_idris_crash('invalid cast: ' + " ++ jsString (show ty) ++ " + ' -> ' + " ++ jsString (show ty2) ++ ")"
jsOp BelieveMe [_,_,x] = x
jsOp (Crash) [_, msg] = "__jsPrim_idris_crash(" ++ jsString msg ++ ")"

jsPrim : Name -> List String -> Core String
jsPrim x args = throw (InternalError $ "prim not implemented: " ++ (show x))

makeForeignFromExp : Name -> Nat -> String -> String
makeForeignFromExp n nargs pattern =
  let lastArg = nargs `minus` 1
  in "const " ++ jsName n ++ " = (" ++ showSep ", " [ "_" ++ show x | x<-[0..lastArg]] ++ ") => " ++ pattern


foreignDecl : Name -> List String -> Core String
foreignDecl n ["C:idris2_putStr,libidris2_support"] =
  pure $ makeForeignFromExp n 2 "process.stdout.write(_0)"
foreignDecl x path = throw (InternalError $ "foreign not supported: " ++ (show path))

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
    pure $ jsOp f !(traverseVect impExp2es args)
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
    in pure $ "{" ++ showSep ", " (("h:" ++ show h)::argPairs) ++ "}"
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
  imperative2es indent (FunDecl n args body) =
    pure $ nSpaces indent ++ "function " ++ jsName n ++ "(" ++ showSep ", " (map jsName args) ++ "){\n" ++
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
    let pre = showSep "\n" $ SortedSet.toList $ preamble st
    pure $ pre ++ "\n\n" ++ es_statements

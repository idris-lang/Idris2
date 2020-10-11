module Compiler.RefC.RefC

import Compiler.Common
import Compiler.CompileExpr
import Compiler.LambdaLift
import Compiler.ANF
import Compiler.Inline

import Core.Context
import Core.Directory
import Core.Name
import Core.Options
import Core.TT

import Data.IORef
import Data.List
import Data.NameMap
import Data.Nat
import Data.Strings
import Data.Vect

import System
import System.Info
import System.File

import Idris.Version
import Utils.Hex
import Utils.Path

findCC : IO String
findCC
    = do Just cc <- getEnv "IDRIS2_CC"
              | Nothing => do Just cc <- getEnv "CC"
                                   | Nothing => pure "cc"
                              pure cc
         pure cc

toString : List Char -> String
toString [] = ""
toString (c :: cx) = cast c ++ toString cx

natMinus : (a,b:Nat) -> Nat
natMinus a b = case isLTE b a of
    (Yes prf) => minus a b
    (No _) => 0

showcCleanStringChar : Char -> String -> String
showcCleanStringChar '+' = ("_plus" ++)
showcCleanStringChar '-' = ("__" ++)
showcCleanStringChar '*' = ("_star" ++)
showcCleanStringChar '/' = ("_slash" ++)
showcCleanStringChar '\\' = ("_backslash" ++)
showcCleanStringChar '<' = ("_lt" ++)
showcCleanStringChar '>' = ("_gt" ++)
showcCleanStringChar '=' = ("_eq" ++)
showcCleanStringChar '&' = ("_and" ++)
showcCleanStringChar '|' = ("_or" ++)
showcCleanStringChar '\'' = ("_tick" ++)
showcCleanStringChar '"' = ("_quotation" ++)
showcCleanStringChar '(' = ("_parenOpen" ++)
showcCleanStringChar ')' = ("_parenClose" ++)
showcCleanStringChar '{' = ("_braceOpen" ++)
showcCleanStringChar '}' = ("_braceClose" ++)
showcCleanStringChar ' ' = ("_" ++)
showcCleanStringChar ':' = ("_colon" ++)
showcCleanStringChar '.' = ("_dot" ++)
showcCleanStringChar '$' = ("_dollar" ++)
showcCleanStringChar ',' = ("_comma" ++)
showcCleanStringChar '#' = ("_number" ++)
showcCleanStringChar '%' = ("_percent" ++)
showcCleanStringChar c
   = if c < chr 32 || c > chr 126
        then (("u" ++ pad (asHex (cast c))) ++)
        else strCons c
  where
    pad : String -> String
    pad str
        = case isLTE (length str) 4 of
               Yes _ => toString (List.replicate (natMinus 4 (length str)) '0') ++ str
               No _ => str

showcCleanString : List Char -> String -> String
showcCleanString [] = id
showcCleanString (c ::cs) = (showcCleanStringChar c) . showcCleanString cs

cCleanString : String -> String
cCleanString cs = showcCleanString (unpack cs) ""

cName : Name -> String
cName (NS ns n) = showNSWithSep "_" ns ++ "_" ++ cName n
cName (UN n) = cCleanString n
cName (MN n i) = cCleanString n ++ "_" ++ cCleanString (show i)
cName (PV n d) = "pat__" ++ cName n
cName (DN _ n) = cName n
cName (Nested i n) = "n__" ++ cCleanString (show i) ++ "_" ++ cName n
cName (CaseBlock x y) = "case__" ++ cCleanString (show x) ++ "_" ++ cCleanString (show y)
cName (WithBlock x y) = "with__" ++ cCleanString (show x) ++ "_" ++ cCleanString (show y)
cName (Resolved i) = "fn__" ++ cCleanString (show i)
cName _ = "UNKNOWNNAME"

escapeChar : Char -> String
escapeChar '\DEL' = "127"
escapeChar '\NUL' = "0"
escapeChar '\SOH' = "1"
escapeChar '\STX' = "2"
escapeChar '\ETX' = "3"
escapeChar '\EOT' = "4"
escapeChar '\ENQ' = "5"
escapeChar '\ACK' = "6"
escapeChar '\BEL' = "7"
escapeChar '\BS' = "8"
escapeChar '\HT' = "9"
escapeChar '\LF' = "10"
escapeChar '\VT' = "11"
escapeChar '\FF' = "12"
escapeChar '\CR' = "13"
escapeChar '\SO' = "14"
escapeChar '\SI' = "15"
escapeChar '\DLE' = "16"
escapeChar '\DC1' = "17"
escapeChar '\DC2' = "18"
escapeChar '\DC3' = "19"
escapeChar '\DC4' = "20"
escapeChar '\NAK' = "21"
escapeChar '\SYN' = "22"
escapeChar '\ETB' = "23"
escapeChar '\CAN' = "24"
escapeChar '\EM' = "25"
escapeChar '\SUB' = "26"
escapeChar '\ESC' = "27"
escapeChar '\FS' = "28"
escapeChar '\GS' = "29"
escapeChar '\RS' = "30"
escapeChar '\US' = "31"
escapeChar c = show c

-- escapeChar '\\' = "'\\\\'"
-- escapeChar c = show c

cStringQuoted : String -> String
cStringQuoted cs = strCons '"' (showCString (unpack cs) "\"")
where
    showCChar : Char -> String -> String
    showCChar '\\' = ("bkslash" ++)
    showCChar c
       = if c < chr 32 || c > chr 126
            then (("\\x" ++ (asHex (cast c))) ++)
            else strCons c
      where
        pad : String -> String
        pad str
            = case isLTE (length str) 2 of
                   --Yes _ => toString (List.replicate (natMinus 4 (length str)) '0') ++ str
                   Yes _ => "0" ++ str
                   No _ => str


    showCString : List Char -> String -> String
    showCString [] = id
    showCString ('"'::cs) = ("\\\"" ++) . showCString cs
    showCString (c ::cs) = (showCChar c) . showCString cs



cConstant : Constant -> String
cConstant (I x) = "(Value*)makeInt32("++ show x ++")" -- (constant #:type 'i32 #:val " ++ show x ++ ")"
cConstant (BI x) = "(Value*)makeInt64("++ show x ++")" --"(constant #:type 'i64 #:val " ++ show x ++ ")"
cConstant (Db x) = "(Value*)makeDouble("++ show x ++")"--"(constant #:type 'double #:val " ++ show x ++ ")"
cConstant (Ch x) = "(Value*)makeChar("++ escapeChar x ++")" --"(constant #:type 'char #:val " ++ escapeChar x ++  ")"
cConstant (Str x) = "(Value*)makeString("++ cStringQuoted x ++")"
  -- = "(constant #:type 'string #:val " ++ cStringQuoted x ++ ")"
cConstant WorldVal = "(Value*)makeWorld()"
cConstant IntType = "i32"
cConstant IntegerType = "i64"
cConstant StringType = "string"
cConstant CharType = "char"
cConstant DoubleType = "double"
cConstant WorldType = "f32"
cConstant (B8 x)   = "(Value*)makeInt8("++ show x ++")" --"(constant #:type 'i64 #:val " ++ show x ++ ")"
cConstant (B16 x)  = "(Value*)makeInt16("++ show x ++")" --"(constant #:type 'i64 #:val " ++ show x ++ ")"
cConstant (B32 x)  = "(Value*)makeInt32("++ show x ++")" --"(constant #:type 'i64 #:val " ++ show x ++ ")"
cConstant (B64 x)  = "(Value*)makeInt64("++ show x ++")" --"(constant #:type 'i64 #:val " ++ show x ++ ")"
cConstant Bits8Type = "Bits8"
cConstant Bits16Type = "Bits16"
cConstant Bits32Type = "Bits32"
cConstant Bits64Type = "Bits64"
cConstant _ = "UNKNOWN"

extractConstant : Constant -> String
extractConstant (I x) = show x
extractConstant (BI x) = show x
extractConstant (Db x) = show x
extractConstant (Ch x) = show x
extractConstant (Str x) = cStringQuoted x
extractConstant (B8 x)  = show x
extractConstant (B16 x)  = show x
extractConstant (B32 x)  = show x
extractConstant (B64 x)  = show x
extractConstant c = "unable_to_extract constant >>" ++ cConstant c ++ "<<"


||| Generate scheme for a plain function.
plainOp : String -> List String -> String
plainOp op args = op ++ "(" ++ (showSep ", " args) ++ ")"


||| Generate scheme for a primitive function.
cOp : PrimFn arity -> Vect arity String -> String
cOp (Neg ty)      [x]       = "-" ++ x
cOp StrLength     [x]       = "stringLength(" ++ x ++ ")"
cOp StrHead       [x]       = "head(" ++ x ++ ")"
cOp StrTail       [x]       = "tail(" ++ x ++ ")"
cOp StrReverse    [x]       = "reverse(" ++ x ++ ")"
cOp (Cast i o)    [x]       = "cast_" ++ (cConstant i) ++ "_to_" ++ (cConstant o) ++ "(" ++ x ++ ")"
cOp DoubleExp     [x]       = "(Value*)makeDouble(exp(unpackDouble(" ++ x ++ ")))"
cOp DoubleLog     [x]       = "(Value*)makeDouble(log(unpackDouble(" ++ x ++ ")))"
cOp DoubleSin     [x]       = "(Value*)makeDouble(sin(unpackDouble(" ++ x ++ ")))"
cOp DoubleCos     [x]       = "(Value*)makeDouble(cos(unpackDouble(" ++ x ++ ")))"
cOp DoubleTan     [x]       = "(Value*)makeDouble(tan(unpackDouble(" ++ x ++ ")))"
cOp DoubleASin    [x]       = "(Value*)makeDouble(asin(unpackDouble(" ++ x ++ ")))"
cOp DoubleACos    [x]       = "(Value*)makeDouble(acos(unpackDouble(" ++ x ++ ")))"
cOp DoubleATan    [x]       = "(Value*)makeDouble(atan(unpackDouble(" ++ x ++ ")))"
cOp DoubleSqrt    [x]       = "(Value*)makeDouble(sqrt(unpackDouble(" ++ x ++ ")))"
cOp DoubleFloor   [x]       = "(Value*)makeDouble(floor(unpackDouble(" ++ x ++ ")))"
cOp DoubleCeiling [x]       = "(Value*)makeDouble(ceil(unpackDouble(" ++ x ++ ")))"
cOp (Add ty)      [x, y]    = "add_" ++  cConstant ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (Sub ty)      [x, y]    = "sub_" ++  cConstant ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (Mul ty)      [x, y]    = "mul_" ++  cConstant ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (Div ty)      [x, y]    = "div_" ++  cConstant ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (Mod ty)      [x, y]    = "mod_" ++  cConstant ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (ShiftL ty)   [x, y]    = "shiftl_" ++  cConstant ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (ShiftR ty)   [x, y]    = "shiftr_" ++  cConstant ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (BAnd ty)     [x, y]    = "and_" ++  cConstant ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (BOr ty)      [x, y]    = "or_" ++  cConstant ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (BXOr ty)     [x, y]    = "xor_" ++  cConstant ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (LT ty)       [x, y]    = "lt_" ++  cConstant ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (GT ty)       [x, y]    = "gt_" ++  cConstant ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (EQ ty)       [x, y]    = "eq_" ++  cConstant ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (LTE ty)      [x, y]    = "lte_" ++  cConstant ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (GTE ty)      [x, y]    = "gte_" ++  cConstant ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp StrIndex      [x, i]    = "strIndex(" ++ x ++ ", " ++ i ++ ")"
cOp StrCons       [x, y]    = "strCons(" ++ x ++ ", " ++ y ++ ")"
cOp StrAppend     [x, y]    = "strAppend(" ++ x ++ ", " ++ y ++ ")"
cOp StrSubstr     [x, y, z] =  "strSubstr(" ++ x ++ ", " ++ y  ++ ", " ++ z ++ ")"
cOp fn args = plainOp (show fn) (toList args)



data ExtPrim = SchemeCall
             | NewIORef | ReadIORef | WriteIORef
             | NewArray | ArrayGet | ArraySet
             | GetField | SetField
             | VoidElim
             | SysOS | SysCodegen
             | OnCollect
             | OnCollectAny
             | Unknown Name

export
Show ExtPrim where
  show SchemeCall = "schemeCall"
  show NewIORef = "newIORef"
  show ReadIORef = "readIORef"
  show WriteIORef = "writeIORef"
  show NewArray = "newArray"
  show ArrayGet = "arrayGet"
  show ArraySet = "arraySet"
  show GetField = "getField"
  show SetField = "setField"
  show VoidElim = "voidElim"
  show SysOS = "sysOS"
  show SysCodegen = "sysCodegen"
  show OnCollect = "onCollect"
  show OnCollectAny = "onCollectAny"
  show (Unknown n) = "Unknown " ++ show n

||| Match on a user given name to get the scheme primitive
toPrim : Name -> ExtPrim
toPrim pn@(NS _ n)
    = cond [(n == UN "prim__schemeCall", SchemeCall),
            (n == UN "prim__newIORef", NewIORef),
            (n == UN "prim__readIORef", ReadIORef),
            (n == UN "prim__writeIORef", WriteIORef),
            (n == UN "prim__newArray", NewArray),
            (n == UN "prim__arrayGet", ArrayGet),
            (n == UN "prim__arraySet", ArraySet),
            (n == UN "prim__getField", GetField),
            (n == UN "prim__setField", SetField),
            (n == UN "void", VoidElim),
            (n == UN "prim__os", SysOS),
            (n == UN "prim__codegen", SysCodegen),
            (n == UN "prim__onCollect", OnCollect),
            (n == UN "prim__onCollectAny", OnCollectAny)
            ]
           (Unknown pn)
toPrim pn = Unknown pn


varName : AVar -> String
varName (ALocal i) = "var_" ++ (show i)
varName (ANull)    = "NULL"

data ArgCounter : Type where
data FunctionDefinitions : Type where
data TemporaryVariableTracker : Type where
data OutfileText : Type where
data IndentLevel : Type where
data ExternalLibs : Type where

getNextCounter : {auto a : Ref ArgCounter Nat} -> Core Nat
getNextCounter = do
    c <- get ArgCounter
    put ArgCounter (S c)
    pure c

registerVariableForAutomaticFreeing : {auto t : Ref TemporaryVariableTracker (List (List String))}
                                   -> String
                                   -> Core ()
registerVariableForAutomaticFreeing var = do
    lists <- get TemporaryVariableTracker
    case lists of
        [] => do
            put TemporaryVariableTracker ([[var]])
            pure ()
        (l :: ls) => do
                put TemporaryVariableTracker ((var :: l) :: ls)
                pure ()

newTemporaryVariableLevel : {auto t : Ref TemporaryVariableTracker (List (List String))} -> Core ()
newTemporaryVariableLevel = do
    lists <- get TemporaryVariableTracker
    put TemporaryVariableTracker ([] :: lists)


getNewVar : {auto a : Ref ArgCounter Nat} -> {auto t : Ref TemporaryVariableTracker (List (List String))} -> Core String
getNewVar = do
    c <- getNextCounter
    let var = "tmp_" ++ show c
    registerVariableForAutomaticFreeing var
    pure var


getNewVarThatWillNotBeFreedAtEndOfBlock : {auto a : Ref ArgCounter Nat} -> Core String
getNewVarThatWillNotBeFreedAtEndOfBlock = do
    c <- getNextCounter
    pure $ "tmp_" ++ show c


maxLineLengthForComment : Nat
maxLineLengthForComment = 60

repeat : {ty:Type} -> (x:ty) -> Nat -> List ty
repeat x Z = []
repeat x (S k) = x :: (repeat x k)


lJust : (line:String) -> (fillPos:Nat) -> (filler:Char) -> String
lJust line fillPos filler =
    case isLTE (length line) fillPos of
        (Yes prf) =>
            let missing = minus fillPos (length line)
                fillBlock = pack (repeat filler missing)
            in
            line ++ fillBlock
        (No _) => line

increaseIndentation : {auto il : Ref IndentLevel Nat} -> Core ()
increaseIndentation = do
    iLevel <- get IndentLevel
    put IndentLevel (S iLevel)
    pure ()

decreaseIndentation : {auto il : Ref IndentLevel Nat} -> Core ()
decreaseIndentation = do
    iLevel <- get IndentLevel
    case iLevel of
        Z => pure ()
        (S k) => do
            put IndentLevel k
            pure ()

indentation : {auto il : Ref IndentLevel Nat} -> Core String
indentation = do
    iLevel <- get IndentLevel
    pure $ pack $ repeat ' '  (4 * iLevel)


emit : {auto oft : Ref OutfileText (List String)} -> {auto il : Ref IndentLevel Nat} -> FC -> String -> Core ()
emit EmptyFC line = do
    lines <- get OutfileText
    indent <- indentation
    put OutfileText (lines ++ [indent ++ line])
    pure ()
emit fc line' = do
    let comment = "// " ++ show fc
    lines <- get OutfileText
    indent <- indentation
    let line = line'
    case isLTE (length (indent ++ line)) maxLineLengthForComment of
        (Yes _) => put OutfileText (lines ++ [ (lJust (indent ++ line) maxLineLengthForComment ' ') ++ " " ++ comment]        )
        (No _)  => put OutfileText (lines ++ [indent ++ line, ((lJust ""   maxLineLengthForComment ' ') ++ " " ++ comment)] )
    pure ()


freeTmpVars : {auto t : Ref TemporaryVariableTracker (List (List String))}
           -> {auto oft : Ref OutfileText (List String)}
           -> {auto il : Ref IndentLevel Nat}
           -> Core $ ()
freeTmpVars = do
    lists <- get TemporaryVariableTracker
    case lists of
        (vars :: varss) => do
            traverse (\v => emit EmptyFC $ "removeReference(" ++ v ++ ");" ) vars
            put TemporaryVariableTracker varss
            pure ()
        [] => pure ()


addExternalLib : {auto e : Ref ExternalLibs (List String)}
              -> String
              -> Core ()
addExternalLib extLib = do
    libs <- get ExternalLibs
    case elem extLib libs of
        True => pure () -- library already in list
        False => do
            put ExternalLibs (extLib :: libs)



makeArglist : {auto a : Ref ArgCounter Nat}
           -> {auto t : Ref TemporaryVariableTracker (List (List String))}
           -> {auto oft : Ref OutfileText (List String)}
           -> {auto il : Ref IndentLevel Nat}
           -> Nat
           -> List AVar
           -> Core (String)
makeArglist missing xs = do
    c <- getNextCounter
    let arglist = "arglist_" ++ (show c)
    emit EmptyFC $  "Value_Arglist *"
                 ++ arglist
                 ++ " = newArglist(" ++ show missing
                 ++ "," ++ show ((length xs) + missing)
                 ++ ");"
    pushArgToArglist arglist xs 0
    pure arglist
where
    pushArgToArglist : String
                    -> List AVar
                    -> Nat
                    -> Core ()
    pushArgToArglist arglist [] k = pure ()
    pushArgToArglist arglist (arg :: args) k = do
        emit EmptyFC $ arglist
                    ++ "->args[" ++ show k ++ "] = "
                    ++ " newReference(" ++ varName arg ++");"
        pushArgToArglist arglist args (S k)

fillConstructorArgs : {auto oft : Ref OutfileText (List String)}
                   -> {auto il : Ref IndentLevel Nat}
                   -> String
                   -> List AVar
                   -> Nat
                   -> Core ()
fillConstructorArgs _ [] _ = pure ()
fillConstructorArgs constructor (v :: vars) k = do
    emit EmptyFC $ constructor ++ "->args["++ show k ++ "] = newReference(" ++ varName v ++");"
    fillConstructorArgs constructor vars (S k)


showTag : Maybe Int -> String
showTag Nothing = "-1"
showTag (Just i) = show i

cArgsVectANF : Vect arity AVar -> Core (Vect arity String)
cArgsVectANF [] = pure []
cArgsVectANF (x :: xs) = pure $  (varName x) :: !(cArgsVectANF xs)

showEitherStringInt : Either String Int -> String
showEitherStringInt (Left s) = s
showEitherStringInt (Right i) = show i

toIntEitherStringInt : Either String Int -> Int -> Int
toIntEitherStringInt (Left s) k = k
toIntEitherStringInt (Right i) _ = i

integer_switch : List AConstAlt -> Bool
integer_switch [] = True
integer_switch (MkAConstAlt c _  :: _) =
    case c of
        (I x) => True
        (BI x) => True
        (Ch x) => True
        _ => False

const2Integer : Constant -> Integer -> Integer
const2Integer c i =
    case c of
        (I x) => cast x
        (BI x) => x
        (Ch x) => cast x
        (B8 x) => cast x
        (B16 x) => cast x
        (B32 x) => cast x
        (B64 x) => x
        _ => i





-- we return for each of the ANF a set of statements and two possible return statements
-- The first one for non-tail statements, the second one for tail statements
-- this way, we can deal with tail calls and tail recursion.
-- The higher-level invocation first executes the normal statements and then
-- assign the return value
record ReturnStatement where
    constructor MkRS
    nonTailCall : String
    tailCall : String


mutual
    copyConstructors : {auto a : Ref ArgCounter Nat}
                    -> {auto t : Ref TemporaryVariableTracker (List (List String))}
                    -> {auto oft : Ref OutfileText (List String)}
                    -> {auto il : Ref IndentLevel Nat}
                    -> String
                    -> List AConAlt
                    -> String
                    -> String
                    -> Nat
                    -> Core $ ()
    copyConstructors _ [] _ _ _ = pure ()
    copyConstructors sc ((MkAConAlt n mTag args body) :: xs) constrFieldVar retValVar k = do
        --(restConstructionCopy, restBody) <- copyConstructors sc xs constrFieldVar retValVar (S k)
        (tag', name') <- getNameTag mTag n
        emit EmptyFC $ constrFieldVar ++ "[" ++ show k ++ "].tag = " ++ tag' ++ ";"
        emit EmptyFC $ constrFieldVar ++ "[" ++ show k ++ "].name = " ++ name' ++ ";"
        copyConstructors sc xs constrFieldVar retValVar (S k)
    where
        getNameTag : {auto a : Ref ArgCounter Nat} -> Maybe Int -> Name -> Core (String, String)
        getNameTag Nothing n = pure ("-1", "\"" ++ cName n ++ "\"")
        getNameTag (Just t) _ = pure (show t, "NULL")


    conBlocks : {auto a : Ref ArgCounter Nat}
             -> {auto t : Ref TemporaryVariableTracker (List (List String))}
             -> {auto oft : Ref OutfileText (List String)}
             -> {auto il : Ref IndentLevel Nat}
             -> (scrutinee:String)
             -> List AConAlt
             -> (returnValueVariable:String)
             -> (nrConBlock:Nat)
             -> Core ()
    conBlocks _ [] _ _ = pure ()
    conBlocks sc ((MkAConAlt n mTag args body) :: xs) retValVar k = do
        emit EmptyFC $ "  case " ++ show k ++ ":"
        emit EmptyFC $ "  {"
        increaseIndentation
        newTemporaryVariableLevel
        varBindLines sc args Z
        assignment <- cStatementsFromANF body
        emit EmptyFC $ retValVar ++ " = " ++ nonTailCall assignment ++ ";"
        freeTmpVars
        emit EmptyFC $ "break;"
        decreaseIndentation
        emit EmptyFC $ "  }"
        conBlocks sc xs retValVar (S k)
    where
        varBindLines : String -> (args : List Int) -> Nat -> Core ()
        varBindLines _ [] _ = pure ()
        varBindLines sc (target :: xs) source = do
            emit EmptyFC $  "Value * var_" ++ show target ++ " = ((Value_Constructor*)" ++ sc ++ ")->args[" ++ show source ++ "];"
            varBindLines sc xs (S source)
            pure ()


    constBlockSwitch : {auto a : Ref ArgCounter Nat}
                       -> {auto t : Ref TemporaryVariableTracker (List (List String))}
                       -> {auto oft : Ref OutfileText (List String)}
                       -> {auto il : Ref IndentLevel Nat}
                       -> (alts:List AConstAlt)
                       -> (retValVar:String)
                       -> (alternativeIntMatcher:Integer)
                       -> Core ()
    constBlockSwitch [] _ _ = pure ()
    constBlockSwitch ((MkAConstAlt c' caseBody) :: alts) retValVar i = do
        let c = const2Integer c' i
        emit EmptyFC $ "  case " ++ show c ++ " :"
        emit EmptyFC "  {"
        increaseIndentation
        newTemporaryVariableLevel
        assignment <- cStatementsFromANF caseBody
        emit EmptyFC $ retValVar ++ " = " ++ nonTailCall assignment ++ ";"
        freeTmpVars
        emit EmptyFC "break;"
        decreaseIndentation
        emit EmptyFC "  }"
        constBlockSwitch alts retValVar (i+1)



    constDefaultBlock : {auto a : Ref ArgCounter Nat}
                     -> {auto t : Ref TemporaryVariableTracker (List (List String))}
                     -> {auto oft : Ref OutfileText (List String)}
                     -> {auto il : Ref IndentLevel Nat}
                     -> (def:Maybe ANF)
                     -> (retValVar:String)
                     -> Core ()
    constDefaultBlock Nothing _ = pure ()
    constDefaultBlock (Just defaultBody) retValVar = do
        emit EmptyFC "  default :"
        emit EmptyFC "  {"
        increaseIndentation
        newTemporaryVariableLevel
        assignment <- cStatementsFromANF defaultBody
        emit EmptyFC $ retValVar ++ " = " ++ nonTailCall assignment ++ ";"
        freeTmpVars
        decreaseIndentation
        emit EmptyFC "  }"



    makeNonIntSwitchStatementConst :
                    {auto a : Ref ArgCounter Nat}
                 -> {auto t : Ref TemporaryVariableTracker (List (List String))}
                 -> {auto oft : Ref OutfileText (List String)}
                 -> {auto il : Ref IndentLevel Nat}
                 -> List AConstAlt
                 -> (k:Int)
                 -> (constantArray:String)
                 -> (compareFct:String)
                 -> Core (String, String)
    makeNonIntSwitchStatementConst [] _ constantArray compareFct  = pure (constantArray, compareFct)
    makeNonIntSwitchStatementConst ((MkAConstAlt constant caseBody) :: alts) 0 _ _ = do
        case constant of
            (Str s) => do
                c <- getNextCounter
                let constantArray = "constantArray_" ++ show c
                emit EmptyFC $ "char **" ++ constantArray ++ " = (char**)malloc(sizeof(char*) * " ++ show (1+(length alts)) ++");"
                makeNonIntSwitchStatementConst ((MkAConstAlt constant caseBody) :: alts) 1 constantArray "multiStringCompare"
            (Db d) => do
                c <- getNextCounter
                let constantArray = "constantArray_" ++ show c
                emit EmptyFC $ "double *" ++ constantArray ++ " = (double*)malloc(sizeof(double) * " ++ show (1+(length alts)) ++");"
                makeNonIntSwitchStatementConst ((MkAConstAlt constant caseBody) :: alts) 1 constantArray "multiDoubleCompare"
            _ => pure ("ERROR_NOT_DOUBLE_OR_STRING", "ERROR_NOT_DOUBLE_OR_STRING")
    makeNonIntSwitchStatementConst ((MkAConstAlt constant caseBody) :: alts) k constantArray compareFct = do
        emit EmptyFC $ constantArray ++ "[" ++ show (k-1) ++ "] = \"" ++ extractConstant constant ++ "\";"
        makeNonIntSwitchStatementConst alts (k+1) constantArray compareFct


    checkTags : List AConAlt -> Core Bool
    checkTags [] = pure False
    checkTags ((MkAConAlt n Nothing args sc) :: xs) = pure False
    checkTags _ = pure True


    cStatementsFromANF : {auto a : Ref ArgCounter Nat}
                      -> {auto t : Ref TemporaryVariableTracker (List (List String))}
                      -> {auto oft : Ref OutfileText (List String)}
                      -> {auto il : Ref IndentLevel Nat}
                      -> ANF
                      -> Core ReturnStatement
    cStatementsFromANF (AV fc x) = do
        let returnLine = "newReference(" ++ varName x  ++ ")"
        pure $ MkRS returnLine returnLine
    cStatementsFromANF (AAppName fc n args) = do
        emit fc $ ("// start " ++ cName n ++ "(" ++ showSep ", " (map (\v => varName v) args) ++ ")")
        arglist <- makeArglist 0 args
        c <- getNextCounter
        let f_ptr_name = "fPtr_" ++ show c
        emit fc $ "Value *(*"++ f_ptr_name ++ ")(Value_Arglist*) = "++  cName n ++ "_arglist;"
        let closure_name = "closure_" ++ show c
        emit fc $ "Value *"
               ++ closure_name
               ++ " = (Value*)makeClosureFromArglist("
               ++ f_ptr_name
               ++ ", "
               ++ arglist
               ++ ");"
        emit fc $ ("// end   " ++ cName n ++ "(" ++ showSep ", " (map (\v => varName v) args) ++ ")")
        pure $ MkRS ("trampoline(" ++ closure_name ++ ")") closure_name
    cStatementsFromANF (AUnderApp fc n missing args) = do
        arglist <- makeArglist missing args
        c <- getNextCounter
        let f_ptr_name = "closure_" ++ show c
        let f_ptr = "Value *(*"++ f_ptr_name ++ ")(Value_Arglist*) = "++  cName n ++ "_arglist;"
        emit fc f_ptr
        let returnLine = "(Value*)makeClosureFromArglist(" ++ f_ptr_name  ++ ", " ++ arglist ++ ")"
        pure $ MkRS returnLine returnLine
    cStatementsFromANF (AApp fc closure arg) =
        -- pure $ "apply_closure(" ++ varName closure ++ ", " ++ varName arg ++ ")"
        pure $ MkRS ("apply_closure(" ++ varName closure ++ ", " ++ varName arg ++ ")")
                    ("tailcall_apply_closure(" ++ varName closure ++ ", " ++ varName arg ++ ")")
    cStatementsFromANF (ALet fc var value body) = do
        valueAssignment <- cStatementsFromANF value
        emit fc $ "Value * var_" ++ (show var) ++ " = " ++ nonTailCall valueAssignment ++ ";"
        registerVariableForAutomaticFreeing $ "var_" ++ (show var)
        bodyAssignment <- cStatementsFromANF body
        pure $ bodyAssignment
    cStatementsFromANF (ACon fc n tag args) = do
        c <- getNextCounter
        let constr = "constructor_" ++ (show c)
        emit fc $ "Value_Constructor* "
                ++ constr ++ " = newConstructor("
                ++ (show (length args))
                ++ ", "  ++ showTag tag  ++ ", "
                ++ "\"" ++ cName n ++ "\""
                ++ ");"
        emit fc $ " // constructor " ++ cName n

        fillConstructorArgs constr args 0
        pure $ MkRS ("(Value*)" ++ constr) ("(Value*)" ++ constr)
        --fillingStatements <- fillConstructorArgs constr args 0
        --pure $ (statement1 :: fillingStatements, "(Value*)" ++ constr ++ ";")
    cStatementsFromANF (AOp fc op args) = do
        argsVec <- cArgsVectANF args
        let opStatement = cOp op argsVec
        pure $ MkRS opStatement opStatement
    cStatementsFromANF (AExtPrim fc p args) = do
        emit fc $ "// call to external primitive " ++ cName p
        let returnLine = (cCleanString (show (toPrim p)) ++ "("++ showSep ", " (map (\v => varName v) args) ++")")
        pure $ MkRS returnLine returnLine
    cStatementsFromANF (AConCase fc sc alts mDef) = do
        c <- getNextCounter
        switchReturnVar <- getNewVarThatWillNotBeFreedAtEndOfBlock
        let newValueLine = "Value * " ++ switchReturnVar ++ " = NULL;"
        let constructorField = "constructorField_" ++ show c
        let constructorFieldLine = "AConAlt * " ++ constructorField
                                ++ "= newConstructorField(" ++ show (length alts) ++ ");"
        let switchLine = "switch(compareConstructors("
                      ++ varName sc
                      ++ ", "
                      ++ constructorField
                      ++ ", "
                      ++ show (length alts)
                      ++ ")){"
        emit fc newValueLine
        emit fc constructorFieldLine
        copyConstructors (varName sc) alts constructorField switchReturnVar 0
        emit fc switchLine
        conBlocks (varName sc) alts switchReturnVar 0
        case mDef of
            Nothing => do
                emit EmptyFC $ "}"
                emit EmptyFC $ "free(" ++ constructorField ++ ");"
                pure $ MkRS switchReturnVar switchReturnVar
            (Just d) => do
                emit EmptyFC $ "  default : {"
                increaseIndentation
                newTemporaryVariableLevel
                defaultAssignment <- cStatementsFromANF d
                -- traverse (\l => emit EmptyFC (l) ) defaultBody
                emit EmptyFC $ switchReturnVar ++ " = " ++ nonTailCall defaultAssignment ++ ";"
                freeTmpVars
                decreaseIndentation
                emit EmptyFC $ "  }"
                emit EmptyFC $ "}"
                -- let defaultBlock = []
                --                 ++ (map (\s => s) defaultBody)
                --                 ++ [defaultLastLine1, defaultLastLine2]
                emit EmptyFC $ "free(" ++ constructorField ++ ");"
                pure $ MkRS switchReturnVar switchReturnVar
    cStatementsFromANF (AConstCase fc sc alts def) = do
        switchReturnVar <- getNewVarThatWillNotBeFreedAtEndOfBlock
        let newValueLine = "Value * " ++ switchReturnVar ++ " = NULL;"
        emit fc newValueLine
        case integer_switch alts of
            True => do
                emit fc $ "switch(extractInt(" ++ varName sc ++")){"
                constBlockSwitch alts switchReturnVar 0
                constDefaultBlock def switchReturnVar
                emit EmptyFC "}"
                pure $ MkRS switchReturnVar switchReturnVar
            False => do
                (compareField, compareFunction) <- makeNonIntSwitchStatementConst alts 0 "" ""
                emit fc $ "switch("++ compareFunction ++ "(" ++ varName sc ++ ", " ++ show (length alts) ++ ", " ++ compareField ++ ")){"
                constBlockSwitch alts switchReturnVar 0
                constDefaultBlock def switchReturnVar
                emit EmptyFC "}"
                emit EmptyFC $ "free(" ++ compareField ++ ");"
                pure $ MkRS switchReturnVar switchReturnVar
    cStatementsFromANF (APrimVal fc c) = pure $ MkRS (cConstant c) (cConstant c)
    cStatementsFromANF (AErased fc) = pure $ MkRS "NULL" "NULL"
    cStatementsFromANF (ACrash fc x) = do
        emit fc $ "// CRASH"
        pure $ MkRS "NULL" "NULL"





readCCPart : Char -> String -> (String, String)
readCCPart b x =
  let (cc, def) = break (== b) x
  in (cc, drop 1 def)
where
    drop : Int -> String -> String
    drop headLength s =
        let len = cast (length s)
            subStrLen = len - headLength in
        strSubstr headLength subStrLen s

extractFFILocation : (lang:String) -> List String -> Maybe (String, String)
extractFFILocation targetLang [] = Nothing
extractFFILocation targetLang (def :: defs) =
    let (thisLang,pos) = readCCPart ':' def in
    case targetLang == thisLang of
        True => Just (readCCPart ',' pos)
        False => extractFFILocation targetLang defs


addCommaToList : List String -> Core $ List String
addCommaToList [] = pure []
addCommaToList (x :: xs) = pure $  ("  " ++ x) :: !(addCommaToList' xs)
where
    addCommaToList' : List String -> Core $ List String
    addCommaToList' [] = pure $ []
    addCommaToList' (x :: xs) = pure $ (", " ++ x) :: !(addCommaToList' xs)


functionDefSignature : {auto c : Ref Ctxt Defs} -> Name -> (args:List Int) -> Core String
functionDefSignature n [] = do
    let fn = (cName !(getFullName n))
    pure $  "\n\nValue *"  ++ fn ++ "(void)"
functionDefSignature n args = do
    argsStringList <- addCommaToList (map (\i =>  "  Value * var_" ++ (show i)) args)
    let fn = (cName !(getFullName n))
    pure $  "\n\nValue *"  ++ fn ++ "\n(\n" ++ (showSep "\n" (argsStringList)) ++ "\n)"

functionDefSignatureArglist : {auto c : Ref Ctxt Defs} -> Name  -> Core String
functionDefSignatureArglist n = pure $  "Value *"  ++ (cName !(getFullName n)) ++ "_arglist(Value_Arglist* arglist)"


getArgsNrList : {ty:Type} -> List ty -> Nat -> Core $ List Nat
getArgsNrList [] _ = pure []
getArgsNrList (x :: xs) k = pure $ k :: !(getArgsNrList xs (S k))


cTypeOfCFType : CFType -> Core $ String
cTypeOfCFType CFUnit          = pure $ ("void")
cTypeOfCFType CFInt           = pure $ ("int")
cTypeOfCFType CFUnsigned8     = pure $ ("uint8_t")
cTypeOfCFType CFUnsigned16    = pure $ ("uint16_t")
cTypeOfCFType CFUnsigned32    = pure $ ("uint32_t")
cTypeOfCFType CFUnsigned64    = pure $ ("uint64_t")
cTypeOfCFType CFString        = pure $ ("char *")
cTypeOfCFType CFDouble        = pure $ ("double")
cTypeOfCFType CFChar          = pure $ ("char")
cTypeOfCFType CFPtr           = pure $ ("void *")
cTypeOfCFType CFGCPtr         = pure $ ("void *")
cTypeOfCFType CFBuffer        = pure $ ("void *")
cTypeOfCFType CFWorld         = pure $ ("void *")
cTypeOfCFType (CFFun x y)     = pure $ ("void *")
cTypeOfCFType (CFIORes x)     = pure $ ("void *")
cTypeOfCFType (CFStruct x ys) = pure $ ("void *")
cTypeOfCFType (CFUser x ys)   = pure $ ("void *")

varNamesFromList : {ty:Type} -> List ty -> Nat -> Core $ List String
varNamesFromList [] _ = pure []
varNamesFromList (x :: xs) k = pure $ ("var_" ++ show k) :: !(varNamesFromList xs (S k))

createFFIArgList : List CFType
                -> Core $ List (String, String, CFType)
createFFIArgList cftypeList = do
    sList <- traverse cTypeOfCFType cftypeList
    varList <- varNamesFromList cftypeList 1
    let z = zip3 sList varList cftypeList
    pure z

emitFDef : {auto oft : Ref OutfileText (List String)}
        -> {auto il : Ref IndentLevel Nat}
        -> (funcName:Name)
        -> (arglist:List (String, String, CFType))
        -> Core ()
emitFDef funcName [] = emit EmptyFC $ cName funcName ++ "(void)"
emitFDef funcName ((varType, varName, varCFType) :: xs) = do
    emit EmptyFC $ "Value *" ++ cName funcName
    emit EmptyFC "("
    increaseIndentation
    emit EmptyFC $ "  Value *" ++ varName
    traverse (\(varType, varName, varCFType) => emit EmptyFC $ ", Value *" ++ varName) xs
    decreaseIndentation
    emit EmptyFC ")"

extractValue : (cfType:CFType) -> (varName:String) -> String
extractValue CFUnit          varName = "void"
extractValue CFInt           varName = "((Value_Int32*)" ++ varName ++ ")->i32"
extractValue CFUnsigned8     varName = "((Value_Int8*)" ++ varName ++ ")->i8"
extractValue CFUnsigned16    varName = "((Value_Int16*)" ++ varName ++ ")->i16"
extractValue CFUnsigned32    varName = "((Value_Int32*)" ++ varName ++ ")->i32"
extractValue CFUnsigned64    varName = "((Value_Int64*)" ++ varName ++ ")->i64"
extractValue CFString        varName = "((Value_String*)" ++ varName ++ ")->str"
extractValue CFDouble        varName = "((Value_Double*)" ++ varName ++ ")->d"
extractValue CFChar          varName = "((Value_Char*)" ++ varName ++ ")->c"
extractValue CFPtr           varName = "((Value_Pointer*)" ++ varName ++ ")->p"
extractValue CFGCPtr         varName = "((Value_GCPointer*)" ++ varName ++ ")->p->p"
extractValue CFBuffer        varName = "((Value_Buffer*)" ++ varName ++ ")->buffer"
extractValue CFWorld         varName = "(Value_World*)" ++ varName
extractValue (CFFun x y)     varName = "Value* " ++ varName ++ "/* function pointer not implemented */"
extractValue (CFIORes x)     varName = extractValue x varName
extractValue (CFStruct x xs) varName = "Value* " ++ varName ++ "/* struct access not implemented */"
extractValue (CFUser x xs)   varName = "Value* " ++ varName

packCFType : (cfType:CFType) -> (varName:String) -> String
packCFType CFUnit          varName = "NULL"
packCFType CFInt           varName = "makeInt32(" ++ varName ++ ")"
packCFType CFUnsigned64    varName = "makeInt64(" ++ varName ++ ")"
packCFType CFUnsigned32    varName = "makeInt32(" ++ varName ++ ")"
packCFType CFUnsigned16    varName = "makeInt16(" ++ varName ++ ")"
packCFType CFUnsigned8     varName = "makeInt8(" ++ varName ++ ")"
packCFType CFString        varName = "makeString(" ++ varName ++ ")"
packCFType CFDouble        varName = "makeDouble(" ++ varName ++ ")"
packCFType CFChar          varName = "makeChar(" ++ varName ++ ")"
packCFType CFPtr           varName = "makePointer(" ++ varName ++ ")"
packCFType CFGCPtr         varName = "makePointer(" ++ varName ++ ")"
packCFType CFBuffer        varName = "makeBuffer(" ++ varName ++ ")"
packCFType CFWorld         varName = "makeWorld(" ++ varName ++ ")"
packCFType (CFFun x y)     varName = "makeFunction(" ++ varName ++ ")"
packCFType (CFIORes x)     varName = packCFType x varName
packCFType (CFStruct x xs) varName = "makeStruct(" ++ varName ++ ")"
packCFType (CFUser x xs)   varName = "makeCustomUser(" ++ varName ++ ")"

discardLastArgument : {ty:Type} -> List ty -> List ty
discardLastArgument [] = []
discardLastArgument (x :: []) = []
discardLastArgument (x :: y :: ys) = x :: (discardLastArgument (y :: ys))



createCFunctions : {auto c : Ref Ctxt Defs}
                -> {auto a : Ref ArgCounter Nat}
                -> {auto f : Ref FunctionDefinitions (List String)}
                -> {auto t : Ref TemporaryVariableTracker (List (List String))}
                -> {auto oft : Ref OutfileText (List String)}
                -> {auto il : Ref IndentLevel Nat}
                -> {auto e : Ref ExternalLibs (List String)}
                -> Name
                -> ANFDef
                -> Core ()
createCFunctions n (MkAFun args anf) = do
    fn <- functionDefSignature n args
    fn' <- functionDefSignatureArglist n
    otherDefs <- get FunctionDefinitions
    put FunctionDefinitions ((fn ++ ";\n") :: (fn' ++ ";\n") :: otherDefs)
    newTemporaryVariableLevel
    argsNrs <- getArgsNrList args Z
    emit EmptyFC fn
    emit EmptyFC "{"
    increaseIndentation
    assignment <- cStatementsFromANF anf
    emit EmptyFC $ "Value *returnValue = " ++ tailCall assignment ++ ";"
    freeTmpVars
    emit EmptyFC $ "return returnValue;"
    decreaseIndentation
    emit EmptyFC  "}\n"
    emit EmptyFC  ""
    emit EmptyFC fn'
    emit EmptyFC "{"
    increaseIndentation
    emit EmptyFC $ "return " ++ (cName !(getFullName n))
    increaseIndentation
    emit EmptyFC $ "("
    increaseIndentation
    commaSepArglist <- addCommaToList (map (\a => "arglist->args["++ show a ++"]") argsNrs)
    traverse (emit EmptyFC) commaSepArglist
    decreaseIndentation
    emit EmptyFC ");"
    decreaseIndentation
    decreaseIndentation
    emit EmptyFC  "}\n"
    emit EmptyFC  ""
    pure ()


createCFunctions n (MkACon tag arity) = do
  emit EmptyFC $ ( "// Constructor tag " ++ show tag ++ " arity " ++ show arity) -- Nothing to compile here
  pure ()


createCFunctions n (MkAForeign ccs fargs (CFIORes ret)) = do
  case extractFFILocation "C" ccs of
      Nothing => case extractFFILocation "scheme" ccs of
          Nothing => pure ()
          (Just (fctName, lib)) => emit EmptyFC $ "// call ffi to a scheme substitute for " ++ fctName
      (Just (fctName, lib)) => do
          addExternalLib lib
          otherDefs <- get FunctionDefinitions
          let fnDef = "Value *" ++ (cName n) ++ "(" ++ showSep ", " (repeat "Value *" (length fargs)) ++ ");"
          fn_arglist <- functionDefSignatureArglist n
          put FunctionDefinitions ((fnDef ++ "\n") :: (fn_arglist ++ ";\n") :: otherDefs)
          typeVarNameArgList <- createFFIArgList fargs

          emit EmptyFC fn_arglist
          emit EmptyFC "{"
          increaseIndentation
          emit EmptyFC $ "return " ++ (cName n)
          increaseIndentation
          emit EmptyFC $ "("
          increaseIndentation
          commaSepArglist <- addCommaToList (map (\a => "arglist->args["++ show a ++"]") !(getArgsNrList fargs Z))
          traverse (emit EmptyFC) commaSepArglist
          decreaseIndentation
          emit EmptyFC ");"
          decreaseIndentation
          decreaseIndentation
          emit EmptyFC  "}\n"
          emit EmptyFC  ""

          emitFDef n typeVarNameArgList
          emit EmptyFC "{"
          increaseIndentation
          emit EmptyFC $ " // ffi call to " ++ fctName
          case ret of
              CFUnit => do
                  emit EmptyFC $ fctName
                              ++ "("
                              ++ showSep ", " (map (\(_, vn, vt) => extractValue vt vn) (discardLastArgument typeVarNameArgList))
                              ++ ");"
                  emit EmptyFC "return NULL;"
                  decreaseIndentation
                  emit EmptyFC "}\n"
              _ => do
                  emit EmptyFC $ !(cTypeOfCFType ret) ++ " retVal = " ++ fctName
                              ++ "("
                              ++ showSep ", " (map (\(_, vn, vt) => extractValue vt vn) (discardLastArgument typeVarNameArgList))
                              ++ ");"
                  emit EmptyFC $ "return (Value*)" ++ packCFType ret "retVal" ++ ";"
                  decreaseIndentation
                  emit EmptyFC "}\n"

          -- decreaseIndentation
          -- emit EmptyFC "}"

          --put FunctionDefinitions ((fn ++ ";\n") :: (fn' ++ ";\n") :: otherDefs)
      --ffiString n fctName lib fargs (CFIORes ret)

createCFunctions n (MkAForeign ccs fargs ret) = pure () -- unable to deal with return values that are not CFIORes
createCFunctions n (MkAError exp) = do
    fn <- functionDefSignature n []
    fn' <- functionDefSignatureArglist n
    otherDefs <- get FunctionDefinitions
    put FunctionDefinitions (fn :: fn' :: otherDefs)
    --(statements, assignment) <- cStatementsFromANF exp
    emit EmptyFC $ fn
        ++ "\n{"
        ++ "fprintf(stderr, \"Error in "  ++ (cName n) ++ "\");\n"
        ++ "exit(-1);\n"
        ++ "return NULL;"
        ++ "\n}"
    pure ()


header : {auto f : Ref FunctionDefinitions (List String)}
      -> {auto o : Ref OutfileText (List String)}
      -> {auto il : Ref IndentLevel Nat}
      -> {auto e : Ref ExternalLibs (List String)}
      -> Core ()
header = do
    let initLines = [ "#include <runtime.h>"
                    , "/* automatically generated using the Idris2 C Backend */"
                    , "#include <idris_support.h> // for libidris2_support"]
    extLibs <- get ExternalLibs
    let extLibLines = map (\lib => "// add header(s) for library: " ++ lib ++ "\n") extLibs
    traverse (\l => coreLift (putStrLn $ " header for " ++ l ++ " needed")) extLibs
    fns <- get FunctionDefinitions
    outText <- get OutfileText
    put OutfileText (initLines ++ extLibLines ++ ["\n// function definitions"] ++ fns ++ outText)
    pure ()

footer : {auto il : Ref IndentLevel Nat} -> {auto f : Ref OutfileText (List String)} -> Core ()
footer = do
    emit EmptyFC ""
    emit EmptyFC " // main function"
    emit EmptyFC "int main()"
    emit EmptyFC "{"
    emit EmptyFC "   Value *mainExprVal = __mainExpression_0();"
    emit EmptyFC "   trampoline(mainExprVal);"
    emit EmptyFC "   return 0; // bye bye"
    emit EmptyFC "}"
    pure ()

export
executeExpr : Ref Ctxt Defs -> (execDir : String) -> ClosedTerm -> Core ()
executeExpr c _ tm
    = do coreLift $ putStrLn "Execute expression not yet implemented for refc"
         coreLift $ system "false"
         pure ()

export
compileExpr : UsePhase
           -> Ref Ctxt Defs
           -> (tmpDir : String)
           -> (outputDir : String)
           -> ClosedTerm
           -> (outfile : String)
           -> Core (Maybe String)
compileExpr ANF c _ outputDir tm outfile =
  do let outn = outputDir </> outfile ++ ".c"
     let outobj = outputDir </> outfile ++ ".o"
     let outexec = outputDir </> outfile

     coreLift $ mkdirAll outputDir
     cdata <- getCompileData ANF tm
     let defs = anf cdata
     newRef ArgCounter 0
     newRef FunctionDefinitions []
     newRef TemporaryVariableTracker []
     newRef OutfileText []
     newRef ExternalLibs []
     newRef IndentLevel 0
     traverse (\(n, d) => createCFunctions n d) defs
     header -- added after the definition traversal in order to add all encountered function defintions
     footer
     fileContent <- get OutfileText
     let code = fastAppend (map (++ "\n") fileContent)

     coreLift (writeFile outn code)
     coreLift $ putStrLn $ "Generated C file " ++ outn

     cc <- coreLift findCC
     dirs <- getDirs

     let runccobj = cc ++ " -c " ++ outn ++ " -o " ++ outobj ++ " " ++
                       "-I" ++ fullprefix_dir dirs "refc " ++
                       "-I" ++ fullprefix_dir dirs "include"

     let runcc = cc ++ " " ++ outobj ++ " -o " ++ outexec ++ " " ++
                       fullprefix_dir dirs "lib" </> "libidris2_support.a" ++ " " ++
                       "-lidris2_refc " ++
                       "-L" ++ fullprefix_dir dirs "refc " ++
                       clibdirs (lib_dirs dirs)

     coreLift $ putStrLn runccobj
     ok <- coreLift $ system runccobj
     if ok == 0
        then do coreLift $ putStrLn runcc
                ok <- coreLift $ system runcc
                if ok == 0
                   then pure (Just outexec)
                   else pure Nothing
        else pure Nothing
  where
    fullprefix_dir : Dirs -> String -> String
    fullprefix_dir dirs sub
        = prefix_dir dirs </> "idris2-" ++ showVersion False version </> sub

    clibdirs : List String -> String
    clibdirs ds = concat (map (\d => "-L" ++ d ++ " ") ds)
compileExpr _ _ _ _ _ _ = pure Nothing

export
codegenRefC : Codegen
codegenRefC = MkCG (compileExpr ANF) executeExpr

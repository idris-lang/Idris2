module Compiler.RefC.RefC

import Compiler.RefC.CC

import Compiler.Common
import Compiler.CompileExpr
import Compiler.ANF
import Compiler.Generated

import Core.Context
import Core.Context.Log
import Core.Directory

import Idris.Syntax

import Data.List
import Libraries.Data.DList
import Data.Nat
import Libraries.Data.SortedSet
import Data.Vect

import System
import System.File

import Protocol.Hex
import Libraries.Utils.Path

%default covering

showcCleanStringChar : Char -> String -> String
showcCleanStringChar ' ' = ("_" ++)
showcCleanStringChar '!' = ("_bang" ++)
showcCleanStringChar '"' = ("_quotation" ++)
showcCleanStringChar '#' = ("_number" ++)
showcCleanStringChar '$' = ("_dollar" ++)
showcCleanStringChar '%' = ("_percent" ++)
showcCleanStringChar '&' = ("_and" ++)
showcCleanStringChar '\'' = ("_tick" ++)
showcCleanStringChar '(' = ("_parenOpen" ++)
showcCleanStringChar ')' = ("_parenClose" ++)
showcCleanStringChar '*' = ("_star" ++)
showcCleanStringChar '+' = ("_plus" ++)
showcCleanStringChar ',' = ("_comma" ++)
showcCleanStringChar '-' = ("__" ++)
showcCleanStringChar '.' = ("_dot" ++)
showcCleanStringChar '/' = ("_slash" ++)
showcCleanStringChar ':' = ("_colon" ++)
showcCleanStringChar ';' = ("_semicolon" ++)
showcCleanStringChar '<' = ("_lt" ++)
showcCleanStringChar '=' = ("_eq" ++)
showcCleanStringChar '>' = ("_gt" ++)
showcCleanStringChar '?' = ("_question" ++)
showcCleanStringChar '@' = ("_at" ++)
showcCleanStringChar '[' = ("_bracketOpen" ++)
showcCleanStringChar '\\' = ("_backslash" ++)
showcCleanStringChar ']' = ("_bracketClose" ++)
showcCleanStringChar '^' = ("_hat" ++)
showcCleanStringChar '_' = ("_" ++)
showcCleanStringChar '`' = ("_backquote" ++)
showcCleanStringChar '{' = ("_braceOpen" ++)
showcCleanStringChar '|' = ("_or" ++)
showcCleanStringChar '}' = ("_braceClose" ++)
showcCleanStringChar '~' = ("_tilde" ++)
showcCleanStringChar c
   = if c < chr 32 || c > chr 126
        then (("u" ++ leftPad '0' 4 (asHex (cast c))) ++)
        else strCons c

showcCleanString : List Char -> String -> String
showcCleanString [] = id
showcCleanString (c ::cs) = (showcCleanStringChar c) . showcCleanString cs

cCleanString : String -> String
cCleanString cs = showcCleanString (unpack cs) ""

export
cUserName : UserName -> String
cUserName (Basic n) = cCleanString n
cUserName (Field n) = "rec__" ++ cCleanString n
cUserName Underscore = cCleanString "_"

export
cName : Name -> String
cName (NS ns n) = cCleanString (showNSWithSep "_" ns) ++ "_" ++ cName n
cName (UN n) = cUserName n
cName (MN n i) = cCleanString n ++ "_" ++ cCleanString (show i)
cName (PV n d) = "pat__" ++ cName n
cName (DN _ n) = cName n
cName (Nested i n) = "n__" ++ cCleanString (show i) ++ "_" ++ cName n
cName (CaseBlock x y) = "case__" ++ cCleanString (show x) ++ "_" ++ cCleanString (show y)
cName (WithBlock x y) = "with__" ++ cCleanString (show x) ++ "_" ++ cCleanString (show y)
cName (Resolved i) = "fn__" ++ cCleanString (show i)

escapeChar : Char -> String
escapeChar c = if isAlphaNum c || isNL c
                  then show c
                  else "(char)" ++ show (ord c)

cStringQuoted : String -> String
cStringQuoted cs = strCons '"' (showCString (unpack cs) "\"")
where
    showCChar : Char -> String -> String
    showCChar '\\' = ("\\\\" ++)
    showCChar c
       = if c < chr 32
            then (("\\x" ++ leftPad '0' 2 (asHex (cast c))) ++ "\"\"" ++)
            else if c < chr 127 then strCons c
            else if c < chr 65536 then (("\\u" ++ leftPad '0' 4 (asHex (cast c))) ++ "\"\"" ++)
            else (("\\U" ++ leftPad '0' 8 (asHex (cast c))) ++ "\"\"" ++)

    showCString : List Char -> String -> String
    showCString [] = id
    showCString ('"'::cs) = ("\\\"" ++) . showCString cs
    showCString (c ::cs) = (showCChar c) . showCString cs

-- deals with C not allowing `-9223372036854775808` as a literal
showIntMin : Int -> String
showIntMin x = if x == -9223372036854775808
    then "INT64_MIN"
    else "INT64_C("++ show x ++")"

showInt64Min : Int64 -> String
showInt64Min x = if x == -9223372036854775808
    then "INT64_MIN"
    else "INT64_C("++ show x ++")"

cPrimType : PrimType -> String
cPrimType IntType = "Int64"
cPrimType Int8Type = "Int8"
cPrimType Int16Type = "Int16"
cPrimType Int32Type = "Int32"
cPrimType Int64Type = "Int64"
cPrimType IntegerType = "Integer"
cPrimType Bits8Type = "Bits8"
cPrimType Bits16Type = "Bits16"
cPrimType Bits32Type = "Bits32"
cPrimType Bits64Type = "Bits64"
cPrimType StringType = "string"
cPrimType CharType = "char"
cPrimType DoubleType = "double"
cPrimType WorldType = "void"

cConstant : Constant -> String
cConstant (I x) = "(Value*)makeInt64("++ showIntMin x ++")"
cConstant (I8 x) = "(Value*)makeInt8(INT8_C("++ show x ++"))"
cConstant (I16 x) = "(Value*)makeInt16(INT16_C("++ show x ++"))"
cConstant (I32 x) = "(Value*)makeInt32(INT32_C("++ show x ++"))"
cConstant (I64 x) = "(Value*)makeInt64("++ showInt64Min x ++")"
cConstant (BI x) = "(Value*)makeIntegerLiteral(\""++ show x ++"\")"
cConstant (B8 x)   = "(Value*)makeBits8(UINT8_C("++ show x ++"))"
cConstant (B16 x)  = "(Value*)makeBits16(UINT16_C("++ show x ++"))"
cConstant (B32 x)  = "(Value*)makeBits32(UINT32_C("++ show x ++"))"
cConstant (B64 x)  = "(Value*)makeBits64(UINT64_C("++ show x ++"))"
cConstant (Db x) = "(Value*)makeDouble("++ show x ++")"
cConstant (Ch x) = "(Value*)makeChar("++ escapeChar x ++")"
cConstant (Str x) = "(Value*)makeString("++ cStringQuoted x ++")"
cConstant (PrT t) = cPrimType t
cConstant WorldVal = "(Value*)NULL"

extractConstant : Constant -> String
extractConstant (I x) = show x
extractConstant (I8 x) = show x
extractConstant (I16 x) = show x
extractConstant (I32 x) = show x
extractConstant (I64 x) = show x
extractConstant (BI x) = show x
extractConstant (Db x) = show x
extractConstant (Ch x) = show x
extractConstant (Str x) = cStringQuoted x
extractConstant (B8 x)  = show x
extractConstant (B16 x)  = show x
extractConstant (B32 x)  = show x
extractConstant (B64 x)  = show x
extractConstant c = assert_total $ idris_crash ("INTERNAL ERROR: Unable to extract constant: " ++ cConstant c)
-- not really total but this way this internal error does not contaminate everything else

||| Generate scheme for a plain function.
plainOp : String -> List String -> String
plainOp op args = op ++ "(" ++ (showSep ", " args) ++ ")"


||| Generate scheme for a primitive function.
cOp : {0 arity : Nat} -> PrimFn arity -> Vect arity String -> String
cOp (Neg ty)      [x]       = "negate_"  ++  cPrimType ty ++ "(" ++ x ++ ")"
cOp StrLength     [x]       = "stringLength(" ++ x ++ ")"
cOp StrHead       [x]       = "head(" ++ x ++ ")"
cOp StrTail       [x]       = "tail(" ++ x ++ ")"
cOp StrReverse    [x]       = "reverse(" ++ x ++ ")"
cOp (Cast i o)    [x]       = "cast_" ++ (cPrimType i) ++ "_to_" ++ (cPrimType o) ++ "(" ++ x ++ ")"
cOp DoubleExp     [x]       = "(Value*)makeDouble(exp(unpackDouble(" ++ x ++ ")))"
cOp DoubleLog     [x]       = "(Value*)makeDouble(log(unpackDouble(" ++ x ++ ")))"
cOp DoublePow     [x, y]    = "(Value*)makeDouble(pow(unpackDouble(" ++ x ++ "), unpackDouble(" ++ y ++ ")))"
cOp DoubleSin     [x]       = "(Value*)makeDouble(sin(unpackDouble(" ++ x ++ ")))"
cOp DoubleCos     [x]       = "(Value*)makeDouble(cos(unpackDouble(" ++ x ++ ")))"
cOp DoubleTan     [x]       = "(Value*)makeDouble(tan(unpackDouble(" ++ x ++ ")))"
cOp DoubleASin    [x]       = "(Value*)makeDouble(asin(unpackDouble(" ++ x ++ ")))"
cOp DoubleACos    [x]       = "(Value*)makeDouble(acos(unpackDouble(" ++ x ++ ")))"
cOp DoubleATan    [x]       = "(Value*)makeDouble(atan(unpackDouble(" ++ x ++ ")))"
cOp DoubleSqrt    [x]       = "(Value*)makeDouble(sqrt(unpackDouble(" ++ x ++ ")))"
cOp DoubleFloor   [x]       = "(Value*)makeDouble(floor(unpackDouble(" ++ x ++ ")))"
cOp DoubleCeiling [x]       = "(Value*)makeDouble(ceil(unpackDouble(" ++ x ++ ")))"
cOp (Add ty)      [x, y]    = "add_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (Sub ty)      [x, y]    = "sub_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (Mul ty)      [x, y]    = "mul_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (Div ty)      [x, y]    = "div_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (Mod ty)      [x, y]    = "mod_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (ShiftL ty)   [x, y]    = "shiftl_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (ShiftR ty)   [x, y]    = "shiftr_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (BAnd ty)     [x, y]    = "and_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (BOr ty)      [x, y]    = "or_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (BXOr ty)     [x, y]    = "xor_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (LT ty)       [x, y]    = "lt_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (GT ty)       [x, y]    = "gt_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (EQ ty)       [x, y]    = "eq_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (LTE ty)      [x, y]    = "lte_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (GTE ty)      [x, y]    = "gte_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp StrIndex      [x, i]    = "strIndex(" ++ x ++ ", " ++ i ++ ")"
cOp StrCons       [x, y]    = "strCons(" ++ x ++ ", " ++ y ++ ")"
cOp StrAppend     [x, y]    = "strAppend(" ++ x ++ ", " ++ y ++ ")"
cOp StrSubstr     [x, y, z] =  "strSubstr(" ++ x ++ ", " ++ y  ++ ", " ++ z ++ ")"
cOp BelieveMe     [_, _, x] = "newReference(" ++ x ++ ")"
cOp Crash         [_, msg]  = "idris2_crash(" ++ msg ++ ");"
cOp fn args = plainOp (show fn) (toList args)



varName : AVar -> String
varName (ALocal i) = "var_" ++ (show i)
varName (ANull)    = "NULL"

data ArgCounter : Type where
data FunctionDefinitions : Type where
data TemporaryVariableTracker : Type where
data IndentLevel : Type where
data HeaderFiles : Type where

------------------------------------------------------------------------
-- Output generation: using a difference list for efficient append

data OutfileText : Type where

Output : Type
Output = DList String

------------------------------------------------------------------------

getNextCounter : {auto a : Ref ArgCounter Nat} -> Core Nat
getNextCounter = do
    c <- get ArgCounter
    put ArgCounter (S c)
    pure c

registerVariableForAutomaticFreeing : {auto t : Ref TemporaryVariableTracker (List (List String))}
                                   -> String
                                   -> Core ()
registerVariableForAutomaticFreeing var
  = update TemporaryVariableTracker $ \case
      [] => [[var]]
      (l :: ls) => ((var :: l) :: ls)

newTemporaryVariableLevel : {auto t : Ref TemporaryVariableTracker (List (List String))} -> Core ()
newTemporaryVariableLevel = update TemporaryVariableTracker ([] ::)


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

lJust : (line:String) -> (fillPos:Nat) -> (filler:Char) -> String
lJust line fillPos filler =
    let n = length line in
    case isLTE n fillPos of
        (Yes prf) =>
            let missing = minus fillPos n
                fillBlock = pack (replicate missing filler)
            in
            line ++ fillBlock
        (No _) => line

increaseIndentation : {auto il : Ref IndentLevel Nat} -> Core ()
increaseIndentation = update IndentLevel S

decreaseIndentation : {auto il : Ref IndentLevel Nat} -> Core ()
decreaseIndentation = update IndentLevel pred

indentation : {auto il : Ref IndentLevel Nat} -> Core String
indentation = do
    iLevel <- get IndentLevel
    pure $ pack $ replicate (4 * iLevel) ' '

emit
  : {auto oft : Ref OutfileText Output} ->
    {auto il : Ref IndentLevel Nat} ->
    FC -> String -> Core ()
emit EmptyFC line = do
    indent <- indentation
    update OutfileText (flip snoc (indent ++ line))
emit fc line = do
    let comment = "// " ++ show fc
    indent <- indentation
    let indentedLine = indent ++ line
    update OutfileText $ case isLTE (length indentedLine) maxLineLengthForComment of
        (Yes _) => flip snoc (lJust indentedLine maxLineLengthForComment ' ' ++ " " ++ comment)
        (No _)  => flip appendR [indentedLine, (lJust ""   maxLineLengthForComment ' ' ++ " " ++ comment)]


freeTmpVars : {auto t : Ref TemporaryVariableTracker (List (List String))}
           -> {auto oft : Ref OutfileText Output}
           -> {auto il : Ref IndentLevel Nat}
           -> Core $ ()
freeTmpVars = do
    lists <- get TemporaryVariableTracker
    case lists of
        (vars :: varss) => do
            traverse_ (\v => emit EmptyFC $ "removeReference(" ++ v ++ ");" ) vars
            put TemporaryVariableTracker varss
        [] => pure ()


addHeader : {auto h : Ref HeaderFiles (SortedSet String)}
         -> String
         -> Core ()
addHeader = update HeaderFiles . insert



makeArglist : {auto a : Ref ArgCounter Nat}
           -> {auto t : Ref TemporaryVariableTracker (List (List String))}
           -> {auto oft : Ref OutfileText Output}
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
                 ++ "," ++ show (length xs + missing)
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

fillConstructorArgs : {auto oft : Ref OutfileText Output}
                   -> {auto il : Ref IndentLevel Nat}
                   -> String
                   -> List AVar
                   -> Nat
                   -> Core ()
fillConstructorArgs _ [] _ = pure ()
fillConstructorArgs cons (v :: vars) k = do
    emit EmptyFC $ cons ++ "->args["++ show k ++ "] = newReference(" ++ varName v ++");"
    fillConstructorArgs cons vars (S k)


showTag : Maybe Int -> String
showTag Nothing = "-1"
showTag (Just i) = show i

cArgsVectANF : {0 arity : Nat} -> Vect arity AVar -> Core (Vect arity String)
cArgsVectANF [] = pure []
cArgsVectANF (x :: xs) = pure $  (varName x) :: !(cArgsVectANF xs)

integer_switch : List AConstAlt -> Bool
integer_switch [] = True
integer_switch (MkAConstAlt c _  :: _) =
    case c of
        (I x) => True
        (I8 x) => True
        (I16 x) => True
        (I32 x) => True
        (I64 x) => True
        (B8 x) => True
        (B16 x) => True
        (B32 x) => True
        (B64 x) => True
        (BI x) => True
        (Ch x) => True
        _ => False

const2Integer : Constant -> Integer -> Integer
const2Integer c i =
    case c of
        (I x) => cast x
        (I8 x) => cast x
        (I16 x) => cast x
        (I32 x) => cast x
        (I64 x) => cast x
        (BI x) => cast x
        (Ch x) => cast x
        (B8 x) => cast x
        (B16 x) => cast x
        (B32 x) => cast x
        (B64 x) => cast x
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

data TailPositionStatus = InTailPosition | NotInTailPosition

callByPosition : TailPositionStatus -> ReturnStatement -> String
callByPosition InTailPosition = tailCall
callByPosition NotInTailPosition = nonTailCall

mutual
    copyConstructors : {auto a : Ref ArgCounter Nat}
                    -> {auto t : Ref TemporaryVariableTracker (List (List String))}
                    -> {auto oft : Ref OutfileText Output}
                    -> {auto il : Ref IndentLevel Nat}
                    -> String
                    -> List AConAlt
                    -> String
                    -> String
                    -> Nat
                    -> Core $ ()
    copyConstructors _ [] _ _ _ = pure ()
    copyConstructors sc ((MkAConAlt n _ mTag args body) :: xs) constrFieldVar retValVar k = do
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
             -> {auto oft : Ref OutfileText Output}
             -> {auto il : Ref IndentLevel Nat}
             -> (scrutinee:String)
             -> List AConAlt
             -> (returnValueVariable:String)
             -> (nrConBlock:Nat)
             -> TailPositionStatus
             -> Core ()
    conBlocks _ [] _ _ _ = pure ()
    conBlocks sc ((MkAConAlt n _ mTag args body) :: xs) retValVar k tailStatus = do
        emit EmptyFC $ "  case " ++ show k ++ ":"
        emit EmptyFC $ "  {"
        increaseIndentation
        newTemporaryVariableLevel
        varBindLines sc args Z
        assignment <- cStatementsFromANF body tailStatus
        emit EmptyFC $ retValVar ++ " = " ++ callByPosition tailStatus assignment ++ ";"
        freeTmpVars
        emit EmptyFC $ "break;"
        decreaseIndentation
        emit EmptyFC $ "  }"
        conBlocks sc xs retValVar (S k) tailStatus
    where
        varBindLines : String -> (args : List Int) -> Nat -> Core ()
        varBindLines _ [] _ = pure ()
        varBindLines sc (target :: xs) source = do
            emit EmptyFC $  "Value * var_" ++ show target ++ " = ((Value_Constructor*)" ++ sc ++ ")->args[" ++ show source ++ "];"
            varBindLines sc xs (S source)
            pure ()


    constBlockSwitch : {auto a : Ref ArgCounter Nat}
                       -> {auto t : Ref TemporaryVariableTracker (List (List String))}
                       -> {auto oft : Ref OutfileText Output}
                       -> {auto il : Ref IndentLevel Nat}
                       -> (alts:List AConstAlt)
                       -> (retValVar:String)
                       -> (alternativeIntMatcher:Integer)
                       -> TailPositionStatus
                       -> Core ()
    constBlockSwitch [] _ _ _ = pure ()
    constBlockSwitch ((MkAConstAlt c' caseBody) :: alts) retValVar i tailStatus = do
        let c = const2Integer c' i
        emit EmptyFC $ "  case " ++ show c ++ " :"
        emit EmptyFC "  {"
        increaseIndentation
        newTemporaryVariableLevel
        assignment <- cStatementsFromANF caseBody tailStatus
        emit EmptyFC $ retValVar ++ " = " ++ callByPosition tailStatus assignment ++ ";"
        freeTmpVars
        emit EmptyFC "break;"
        decreaseIndentation
        emit EmptyFC "  }"
        constBlockSwitch alts retValVar (i+1) tailStatus



    constDefaultBlock : {auto a : Ref ArgCounter Nat}
                     -> {auto t : Ref TemporaryVariableTracker (List (List String))}
                     -> {auto oft : Ref OutfileText Output}
                     -> {auto il : Ref IndentLevel Nat}
                     -> (def:Maybe ANF)
                     -> (retValVar:String)
                     -> TailPositionStatus
                     -> Core ()
    constDefaultBlock Nothing _ _ = pure ()
    constDefaultBlock (Just defaultBody) retValVar tailStatus = do
        emit EmptyFC "  default :"
        emit EmptyFC "  {"
        increaseIndentation
        newTemporaryVariableLevel
        assignment <- cStatementsFromANF defaultBody tailStatus
        emit EmptyFC $ retValVar ++ " = " ++ callByPosition tailStatus assignment ++ ";"
        freeTmpVars
        decreaseIndentation
        emit EmptyFC "  }"



    makeNonIntSwitchStatementConst :
                    {auto a : Ref ArgCounter Nat}
                 -> {auto t : Ref TemporaryVariableTracker (List (List String))}
                 -> {auto oft : Ref OutfileText Output}
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
        emit EmptyFC $ constantArray ++ "[" ++ show (k-1) ++ "] = " ++ extractConstant constant ++ ";"
        makeNonIntSwitchStatementConst alts (k+1) constantArray compareFct


    checkTags : List AConAlt -> Core Bool
    checkTags [] = pure False
    checkTags ((MkAConAlt n _ Nothing args sc) :: xs) = pure False
    checkTags _ = pure True


    cStatementsFromANF : {auto a : Ref ArgCounter Nat}
                      -> {auto t : Ref TemporaryVariableTracker (List (List String))}
                      -> {auto oft : Ref OutfileText Output}
                      -> {auto il : Ref IndentLevel Nat}
                      -> ANF
                      -> TailPositionStatus
                      -> Core ReturnStatement
    cStatementsFromANF (AV fc x) _ = do
        let returnLine = "newReference(" ++ varName x  ++ ")"
        pure $ MkRS returnLine returnLine
    cStatementsFromANF (AAppName fc _ n args) _ = do
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
    cStatementsFromANF (AUnderApp fc n missing args) _ = do
        arglist <- makeArglist missing args
        c <- getNextCounter
        let f_ptr_name = "closure_" ++ show c
        let f_ptr = "Value *(*"++ f_ptr_name ++ ")(Value_Arglist*) = "++  cName n ++ "_arglist;"
        emit fc f_ptr
        let returnLine = "(Value*)makeClosureFromArglist(" ++ f_ptr_name  ++ ", " ++ arglist ++ ")"
        pure $ MkRS returnLine returnLine
    cStatementsFromANF (AApp fc _ closure arg) _ =
        pure $ MkRS ("apply_closure(" ++ varName closure ++ ", " ++ varName arg ++ ")")
                    ("tailcall_apply_closure(" ++ varName closure ++ ", " ++ varName arg ++ ")")
    cStatementsFromANF (ALet fc var value body) tailPosition = do
        valueAssignment <- cStatementsFromANF value NotInTailPosition
        emit fc $ "Value * var_" ++ (show var) ++ " = " ++ nonTailCall valueAssignment ++ ";"
        registerVariableForAutomaticFreeing $ "var_" ++ (show var)
        bodyAssignment <- cStatementsFromANF body tailPosition
        pure $ bodyAssignment
    cStatementsFromANF (ACon fc n UNIT tag []) _ = do
        pure $ MkRS "(Value*)NULL" "(Value*)NULL"
    cStatementsFromANF (ACon fc n _ tag args) _ = do
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
    cStatementsFromANF (AOp fc _ op args) _ = do
        argsVec <- cArgsVectANF args
        let opStatement = cOp op argsVec
        pure $ MkRS opStatement opStatement
    cStatementsFromANF (AExtPrim fc _ p args) _ = do
        let prims : List String =
            ["prim__newIORef", "prim__readIORef", "prim__writeIORef", "prim__newArray",
             "prim__arrayGet", "prim__arraySet", "prim__getField", "prim__setField",
             "prim__void", "prim__os", "prim__codegen", "prim__onCollect", "prim__onCollectAny" ]
        case p of
            NS _ (UN (Basic pn)) =>
               unless (elem pn prims) $ throw $ InternalError $ "INTERNAL ERROR: Unknown primitive: " ++ cName p
            _ => throw $ InternalError $ "INTERNAL ERROR: Unknown primitive: " ++ cName p
        emit fc $ "// call to external primitive " ++ cName p
        let returnLine = "idris2_" ++ (cName p) ++ "("++ showSep ", " (map varName args) ++")"
        pure $ MkRS returnLine returnLine
    cStatementsFromANF (AConCase fc sc alts mDef) tailPosition = do
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
        conBlocks (varName sc) alts switchReturnVar 0 tailPosition
        case mDef of
            Nothing => do
                emit EmptyFC $ "}"
                emit EmptyFC $ "free(" ++ constructorField ++ ");"
                pure $ MkRS switchReturnVar switchReturnVar
            (Just d) => do
                emit EmptyFC $ "  default : {"
                increaseIndentation
                newTemporaryVariableLevel
                defaultAssignment <- cStatementsFromANF d tailPosition
                emit EmptyFC $ switchReturnVar ++ " = " ++ callByPosition tailPosition defaultAssignment ++ ";"
                freeTmpVars
                decreaseIndentation
                emit EmptyFC $ "  }"
                emit EmptyFC $ "}"
                emit EmptyFC $ "free(" ++ constructorField ++ ");"
                pure $ MkRS switchReturnVar switchReturnVar
    cStatementsFromANF (AConstCase fc sc alts def) tailPosition = do
        switchReturnVar <- getNewVarThatWillNotBeFreedAtEndOfBlock
        let newValueLine = "Value * " ++ switchReturnVar ++ " = NULL;"
        emit fc newValueLine
        case integer_switch alts of
            True => do
                emit fc $ "switch(extractInt(" ++ varName sc ++")){"
                constBlockSwitch alts switchReturnVar 0 tailPosition
                constDefaultBlock def switchReturnVar tailPosition
                emit EmptyFC "}"
                pure $ MkRS switchReturnVar switchReturnVar
            False => do
                (compareField, compareFunction) <- makeNonIntSwitchStatementConst alts 0 "" ""
                emit fc $ "switch("++ compareFunction ++ "(" ++ varName sc ++ ", " ++ show (length alts) ++ ", " ++ compareField ++ ")){"
                constBlockSwitch alts switchReturnVar 0 tailPosition
                constDefaultBlock def switchReturnVar tailPosition
                emit EmptyFC "}"
                emit EmptyFC $ "free(" ++ compareField ++ ");"
                pure $ MkRS switchReturnVar switchReturnVar
    cStatementsFromANF (APrimVal fc c) _ = pure $ MkRS (cConstant c) (cConstant c)
    cStatementsFromANF (AErased fc) _ = pure $ MkRS "NULL" "NULL"
    cStatementsFromANF (ACrash fc x) _ = do
        emit fc $ "// CRASH"
        pure $ MkRS "NULL" "NULL"





addCommaToList : List String -> List String
addCommaToList [] = []
addCommaToList (x :: xs) = ("  " ++ x) :: map (", " ++) xs

functionDefSignature : {auto c : Ref Ctxt Defs} -> Name -> (args:List Int) -> Core String
functionDefSignature n [] = do
    let fn = (cName !(getFullName n))
    pure $  "\n\nValue *"  ++ fn ++ "(void)"
functionDefSignature n args = do
    let argsStringList = addCommaToList (map (\i =>  "  Value * var_" ++ (show i)) args)
    let fn = (cName !(getFullName n))
    pure $  "\n\nValue *"  ++ fn ++ "\n(\n" ++ (showSep "\n" (argsStringList)) ++ "\n)"

functionDefSignatureArglist : {auto c : Ref Ctxt Defs} -> Name  -> Core String
functionDefSignatureArglist n = pure $  "Value *"  ++ (cName !(getFullName n)) ++ "_arglist(Value_Arglist* arglist)"


getArgsNrList : List ty -> Nat -> List Nat
getArgsNrList [] _ = []
getArgsNrList (x :: xs) k = k :: getArgsNrList xs (S k)


cTypeOfCFType : CFType -> String
cTypeOfCFType CFUnit          = "void"
cTypeOfCFType CFInt           = "int64_t"
cTypeOfCFType CFUnsigned8     = "uint8_t"
cTypeOfCFType CFUnsigned16    = "uint16_t"
cTypeOfCFType CFUnsigned32    = "uint32_t"
cTypeOfCFType CFUnsigned64    = "uint64_t"
cTypeOfCFType CFString        = "char *"
cTypeOfCFType CFDouble        = "double"
cTypeOfCFType CFChar          = "char"
cTypeOfCFType CFPtr           = "void *"
cTypeOfCFType CFGCPtr         = "void *"
cTypeOfCFType CFBuffer        = "void *"
cTypeOfCFType CFWorld         = "void *"
cTypeOfCFType (CFFun x y)     = "void *"
cTypeOfCFType (CFIORes x)     = "void *"
cTypeOfCFType (CFStruct x ys) = "void *"
cTypeOfCFType (CFUser x ys)   = "void *"
cTypeOfCFType n = assert_total $ idris_crash ("INTERNAL ERROR: Unknonw FFI type in C backend: " ++ show n)

varNamesFromList : List ty -> Nat -> List String
varNamesFromList str k = map (("var_" ++) . show) (getArgsNrList str k)

createFFIArgList : List CFType
                -> Core $ List (String, String, CFType)
createFFIArgList cftypeList = do
    let sList = map cTypeOfCFType cftypeList
    let varList = varNamesFromList cftypeList 1
    pure $ zip3 sList varList cftypeList

emitFDef : {auto oft : Ref OutfileText Output}
        -> {auto il : Ref IndentLevel Nat}
        -> (funcName:Name)
        -> (arglist:List (String, String, CFType))
        -> Core ()
emitFDef funcName [] = emit EmptyFC $ "Value *" ++ cName funcName ++ "(void)"
emitFDef funcName ((varType, varName, varCFType) :: xs) = do
    emit EmptyFC $ "Value *" ++ cName funcName
    emit EmptyFC "("
    increaseIndentation
    emit EmptyFC $ "  Value *" ++ varName
    traverse_ (\(varType, varName, varCFType) => emit EmptyFC $ ", Value *" ++ varName) xs
    decreaseIndentation
    emit EmptyFC ")"

-- Generic C parameter or RefC specific parameter
data CLang = CLangC | CLangRefC

extractValue : (cLang : CLang) -> (cfType:CFType) -> (varName:String) -> String
extractValue _ CFUnit           varName = "NULL"
extractValue _ CFInt            varName = "((Value_Int64*)" ++ varName ++ ")->i64"
extractValue _ CFInt8           varName = "((Value_Int8*)" ++ varName ++ ")->i8"
extractValue _ CFInt16          varName = "((Value_Int16*)" ++ varName ++ ")->i16"
extractValue _ CFInt32          varName = "((Value_Int32*)" ++ varName ++ ")->i32"
extractValue _ CFInt64          varName = "((Value_Int64*)" ++ varName ++ ")->i64"
extractValue _ CFUnsigned8      varName = "((Value_Bits8*)" ++ varName ++ ")->ui8"
extractValue _ CFUnsigned16     varName = "((Value_Bits16*)" ++ varName ++ ")->ui16"
extractValue _ CFUnsigned32     varName = "((Value_Bits32*)" ++ varName ++ ")->ui32"
extractValue _ CFUnsigned64     varName = "((Value_Bits64*)" ++ varName ++ ")->ui64"
extractValue _ CFString         varName = "((Value_String*)" ++ varName ++ ")->str"
extractValue _ CFDouble         varName = "((Value_Double*)" ++ varName ++ ")->d"
extractValue _ CFChar           varName = "((Value_Char*)" ++ varName ++ ")->c"
extractValue _ CFPtr            varName = "((Value_Pointer*)" ++ varName ++ ")->p"
extractValue _ CFGCPtr          varName = "((Value_GCPointer*)" ++ varName ++ ")->p->p"
extractValue CLangC    CFBuffer varName = "((Value_Buffer*)" ++ varName ++ ")->buffer->data"
extractValue CLangRefC CFBuffer varName = "((Value_Buffer*)" ++ varName ++ ")->buffer"
extractValue _ CFWorld          _       = "(Value *)NULL"
extractValue _ (CFFun x y)      varName = "(Value_Closure*)" ++ varName
extractValue c (CFIORes x)      varName = extractValue c x varName
extractValue _ (CFStruct x xs)  varName = assert_total $ idris_crash ("INTERNAL ERROR: Struct access not implemented: " ++ varName)
-- not really total but this way this internal error does not contaminate everything else
extractValue _ (CFUser x xs)    varName = "(Value*)" ++ varName
extractValue _ n _ = assert_total $ idris_crash ("INTERNAL ERROR: Unknonw FFI type in C backend: " ++ show n)

packCFType : (cfType:CFType) -> (varName:String) -> String
packCFType CFUnit          varName = "NULL"
packCFType CFInt           varName = "makeInt64(" ++ varName ++ ")"
packCFType CFInt8          varName = "makeInt8(" ++ varName ++ ")"
packCFType CFInt16         varName = "makeInt16(" ++ varName ++ ")"
packCFType CFInt32         varName = "makeInt32(" ++ varName ++ ")"
packCFType CFInt64         varName = "makeInt64(" ++ varName ++ ")"
packCFType CFUnsigned64    varName = "makeBits64(" ++ varName ++ ")"
packCFType CFUnsigned32    varName = "makeBits32(" ++ varName ++ ")"
packCFType CFUnsigned16    varName = "makeBits16(" ++ varName ++ ")"
packCFType CFUnsigned8     varName = "makeBits8(" ++ varName ++ ")"
packCFType CFString        varName = "makeString(" ++ varName ++ ")"
packCFType CFDouble        varName = "makeDouble(" ++ varName ++ ")"
packCFType CFChar          varName = "makeChar(" ++ varName ++ ")"
packCFType CFPtr           varName = "makePointer(" ++ varName ++ ")"
packCFType CFGCPtr         varName = "makePointer(" ++ varName ++ ")"
packCFType CFBuffer        varName = "makeBuffer(" ++ varName ++ ")"
packCFType CFWorld         _       = "(Value *)NULL"
packCFType (CFFun x y)     varName = "makeFunction(" ++ varName ++ ")"
packCFType (CFIORes x)     varName = packCFType x varName
packCFType (CFStruct x xs) varName = "makeStruct(" ++ varName ++ ")"
packCFType (CFUser x xs)   varName = varName
packCFType n _ = assert_total $ idris_crash ("INTERNAL ERROR: Unknonw FFI type in C backend: " ++ show n)

discardLastArgument : List ty -> List ty
discardLastArgument [] = []
discardLastArgument xs@(_ :: _) = init xs

additionalFFIStub : Name -> List CFType -> CFType -> String
additionalFFIStub name argTypes (CFIORes retType) = additionalFFIStub name (discardLastArgument argTypes) retType
additionalFFIStub name argTypes retType =
    cTypeOfCFType retType ++
    " (*" ++ cName name ++ ")(" ++
    (concat $ intersperse ", " $ map cTypeOfCFType argTypes) ++ ") = (void*)missing_ffi;\n"

createCFunctions : {auto c : Ref Ctxt Defs}
                -> {auto a : Ref ArgCounter Nat}
                -> {auto f : Ref FunctionDefinitions (List String)}
                -> {auto t : Ref TemporaryVariableTracker (List (List String))}
                -> {auto oft : Ref OutfileText Output}
                -> {auto il : Ref IndentLevel Nat}
                -> {auto h : Ref HeaderFiles (SortedSet String)}
                -> {default [] additionalFFILangs : List String}
                -> Name
                -> ANFDef
                -> Core ()
createCFunctions n (MkAFun args anf) = do
    fn <- functionDefSignature n args
    fn' <- functionDefSignatureArglist n
    update FunctionDefinitions $ \otherDefs => (fn ++ ";\n") :: (fn' ++ ";\n") :: otherDefs
    newTemporaryVariableLevel
    let argsNrs = getArgsNrList args Z
    emit EmptyFC fn
    emit EmptyFC "{"
    increaseIndentation
    assignment <- cStatementsFromANF anf InTailPosition
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
    let commaSepArglist = addCommaToList (map (\a => "arglist->args["++ show a ++"]") argsNrs)
    traverse_ (emit EmptyFC) commaSepArglist
    decreaseIndentation
    emit EmptyFC ");"
    decreaseIndentation
    decreaseIndentation
    emit EmptyFC  "}\n"
    emit EmptyFC  ""
    pure ()


createCFunctions n (MkACon tag arity nt) = do
  emit EmptyFC $ ( "// Constructor tag " ++ show tag ++ " arity " ++ show arity) -- Nothing to compile here


createCFunctions n (MkAForeign ccs fargs ret) = do
  case parseCC (additionalFFILangs ++ ["RefC", "C"]) ccs of
      Just (lang, fctForeignName :: extLibOpts) => do
          let cLang = if lang == "RefC"
                         then CLangRefC
                         else CLangC
          let isStandardFFI = elem lang $ the (List String) ["RefC", "C"]
          let fctName = if isStandardFFI
                           then UN $ Basic $ fctForeignName
                           else NS (mkNamespace lang) n
          if isStandardFFI
             then case extLibOpts of
                      [lib, header] => addHeader header
                      _ => pure ()
             else emit EmptyFC $ additionalFFIStub fctName fargs ret
          let fnDef = "Value *" ++ (cName n) ++ "(" ++ showSep ", " (replicate (length fargs) "Value *") ++ ");"
          fn_arglist <- functionDefSignatureArglist n
          update FunctionDefinitions $ \otherDefs => (fnDef ++ "\n") :: (fn_arglist ++ ";\n") :: otherDefs
          typeVarNameArgList <- createFFIArgList fargs

          emit EmptyFC fn_arglist
          emit EmptyFC "{"
          increaseIndentation
          emit EmptyFC $ "return " ++ (cName n)
          increaseIndentation
          emit EmptyFC $ "("
          increaseIndentation
          let commaSepArglist = addCommaToList (map (\a => "arglist->args["++ show a ++"]") (getArgsNrList fargs Z))
          traverse_ (emit EmptyFC) commaSepArglist
          decreaseIndentation
          emit EmptyFC ");"
          decreaseIndentation
          decreaseIndentation
          emit EmptyFC  "}\n"
          emit EmptyFC  ""

          emitFDef n typeVarNameArgList
          emit EmptyFC "{"
          increaseIndentation
          emit EmptyFC $ " // ffi call to " ++ cName fctName
          case ret of
              CFIORes CFUnit => do
                  emit EmptyFC $ cName fctName
                              ++ "("
                              ++ showSep ", " (map (\(_, vn, vt) => extractValue cLang vt vn) (discardLastArgument typeVarNameArgList))
                              ++ ");"
                  emit EmptyFC "return NULL;"
              CFIORes ret => do
                  emit EmptyFC $ cTypeOfCFType ret ++ " retVal = " ++ cName fctName
                              ++ "("
                              ++ showSep ", " (map (\(_, vn, vt) => extractValue cLang vt vn) (discardLastArgument typeVarNameArgList))
                              ++ ");"
                  emit EmptyFC $ "return (Value*)" ++ packCFType ret "retVal" ++ ";"
              _ => do
                  emit EmptyFC $ cTypeOfCFType ret ++ " retVal = " ++ cName fctName
                              ++ "("
                              ++ showSep ", " (map (\(_, vn, vt) => extractValue cLang vt vn) typeVarNameArgList)
                              ++ ");"
                  emit EmptyFC $ "return (Value*)" ++ packCFType ret "retVal" ++ ";"

          decreaseIndentation
          emit EmptyFC "}"
      _ => assert_total $ idris_crash ("INTERNAL ERROR: FFI not found for " ++ cName n)
          -- not really total but this way this internal error does not contaminate everything else

createCFunctions n (MkAError exp) = assert_total $ idris_crash ("INTERNAL ERROR: Error with expression: " ++ show exp)
-- not really total but this way this internal error does not contaminate everything else

header : {auto c : Ref Ctxt Defs}
      -> {auto f : Ref FunctionDefinitions (List String)}
      -> {auto o : Ref OutfileText Output}
      -> {auto il : Ref IndentLevel Nat}
      -> {auto h : Ref HeaderFiles (SortedSet String)}
      -> Core ()
header = do
    let initLines = """
      #include <runtime.h>
      /* \{ generatedString "RefC" } */

      """
    let headerFiles = Libraries.Data.SortedSet.toList !(get HeaderFiles)
    let headerLines = map (\h => "#include <" ++ h ++ ">\n") headerFiles
    fns <- get FunctionDefinitions
    update OutfileText (appendL ([initLines] ++ headerLines ++ ["\n// function definitions"] ++ fns))

footer : {auto il : Ref IndentLevel Nat}
      -> {auto f : Ref OutfileText Output}
      -> {auto h : Ref HeaderFiles (SortedSet String)}
      -> Core ()
footer = do
    emit EmptyFC """

      // main function
      int main(int argc, char *argv[])
      {
          \{ ifThenElse (contains "idris_support.h" !(get HeaderFiles))
                        "idris2_setArgs(argc, argv);"
                        ""
          }
          Value *mainExprVal = __mainExpression_0();
          trampoline(mainExprVal);
          return 0; // bye bye
      }
      """

export
generateCSourceFile : {auto c : Ref Ctxt Defs}
                   -> {default [] additionalFFILangs : List String}
                   -> List (Name, ANFDef)
                   -> (outn : String)
                   -> Core ()
generateCSourceFile defs outn =
  do _ <- newRef ArgCounter 0
     _ <- newRef FunctionDefinitions []
     _ <- newRef TemporaryVariableTracker []
     _ <- newRef OutfileText DList.Nil
     _ <- newRef HeaderFiles empty
     _ <- newRef IndentLevel 0
     traverse_ (uncurry $ createCFunctions {additionalFFILangs}) defs
     header -- added after the definition traversal in order to add all encountered function defintions
     footer
     fileContent <- get OutfileText
     let code = fastConcat (map (++ "\n") (reify fileContent))

     coreLift_ $ writeFile outn code
     log "compiler.refc" 10 $ "Generated C file " ++ outn

export
compileExpr : UsePhase
           -> Ref Ctxt Defs
           -> Ref Syn SyntaxInfo
           -> (tmpDir : String)
           -> (outputDir : String)
           -> ClosedTerm
           -> (outfile : String)
           -> Core (Maybe String)
compileExpr ANF c s _ outputDir tm outfile =
  do let outn = outputDir </> outfile ++ ".c"
     let outobj = outputDir </> outfile ++ ".o"
     let outexec = outputDir </> outfile

     coreLift_ $ mkdirAll outputDir
     cdata <- getCompileData False ANF tm
     let defs = anf cdata

     generateCSourceFile defs outn
     Just _ <- compileCObjectFile outn outobj
       | Nothing => pure Nothing
     compileCFile outobj outexec

compileExpr _ _ _ _ _ _ _ = pure Nothing



export
executeExpr : Ref Ctxt Defs -> Ref Syn SyntaxInfo ->
              (execDir : String) -> ClosedTerm -> Core ()
executeExpr c s tmpDir tm = do
  do let outfile = "_tmp_refc"
     Just _ <- compileExpr ANF c s tmpDir tmpDir tm outfile
       | Nothing => do coreLift_ $ putStrLn "Error: failed to compile"
     coreLift_ $ system (tmpDir </> outfile)

export
codegenRefC : Codegen
codegenRefC = MkCG (compileExpr ANF) executeExpr Nothing Nothing

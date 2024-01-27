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


fillConstructorArgs : {auto oft : Ref OutfileText Output}
                   -> {auto il : Ref IndentLevel Nat}
                   -> String
                   -> List AVar
                   -> Bits8
                   -> Core ()
fillConstructorArgs _ [] _ = pure ()
fillConstructorArgs cons (v :: vars) k = do
    emit EmptyFC $ cons ++ "->args["++ show k ++ "] = newReference(" ++ varName v ++");"
    fillConstructorArgs cons vars (k + 1)

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


data TailPositionStatus = InTailPosition | NotInTailPosition
data AssignTo = NoYetDcl String | AlreadyDcl String

assignToName : AssignTo -> String
assignToName (NoYetDcl x) = x
assignToName (AlreadyDcl x) = x

emitAssign : {auto oft : Ref OutfileText Output}
                -> {auto il : Ref IndentLevel Nat}
                -> FC -> AssignTo -> String -> Core ()
emitAssign fc assignto rhs = case assignto of
      NoYetDcl x   => emit fc "Value *\{x} = \{rhs};"
      AlreadyDcl x => emit fc "\{x} = \{rhs};"



-- When changing this number, also change idris2_dispatch_closure in runtime.c.
-- Increasing this number will worsen stack consumption and increase the codesize of idris2_dispatch_closure.
-- In C89, the maximum number of arguments is 31, so it should not be larger than 31. 127 is safe in C99, but I do not recommend it.
MaxExtractFunArgs : Nat
MaxExtractFunArgs = 16


cStatementsFromANF : {auto a : Ref ArgCounter Nat}
                      -> {auto t : Ref TemporaryVariableTracker (List (List String))}
                      -> {auto oft : Ref OutfileText Output}
                      -> {auto il : Ref IndentLevel Nat}
                      -> ANF -> AssignTo
                      -> TailPositionStatus
                      -> Core ()

concaseBody : {auto a : Ref ArgCounter Nat}
             -> {auto t : Ref TemporaryVariableTracker (List (List String))}
             -> {auto oft : Ref OutfileText Output}
             -> {auto il : Ref IndentLevel Nat}
             -> String -> String -> List Int -> ANF -> TailPositionStatus
             -> Core ()
concaseBody returnvar expr args bdy tailstatus = do
    increaseIndentation
    newTemporaryVariableLevel
    _ <- foldlC (\k, arg => do
        emit emptyFC "Value *var_\{show arg} = ((Value_Constructor*)\{expr})->args[\{show k}];"
        pure (S k) ) 0 args
    cStatementsFromANF bdy (AlreadyDcl returnvar) tailstatus
    freeTmpVars
    decreaseIndentation

cStatementsFromANF (AV fc x) lh _ = emitAssign fc lh "newReference(\{varName x})"
cStatementsFromANF (AAppName fc _ n args) lh tailstatus = do
    emit fc $ ("// start " ++ cName n ++ "(" ++ showSep ", " (map (\v => varName v) args) ++ ")")
    let nargs = length args
    case tailstatus of
        InTailPosition    => do
            emitAssign fc lh "makeClosure((Value *(*)())\{cName n}, \{show nargs}, \{show nargs})"
            fillConstructorArgs "((Value_Constructor*)\{assignToName lh})" args 0
        NotInTailPosition => do
            if nargs > MaxExtractFunArgs
                then do
                    emitAssign fc lh "NULL"
                    let lh' = AlreadyDcl $ assignToName lh
                    emit fc "{"
                    increaseIndentation
                    if nargs > 256
                        then do
                            emit fc "Value **local_arglist = idris2_malloc(sizeof(Value *) * \{show nargs});"
                            _ <- foldlC (\i, n => do
                                    emit fc "local_arglist[\{show i}] = \{varName n};"
                                    pure (i + 1)) 0 args
                            emitAssign fc lh' "\{cName n}(local_arglist)"
                            emit fc "idris2_free(local_arglist);"
                            emitAssign fc lh' "trampoline(\{assignToName lh})"
                        else do
                            emit fc "Value *local_arglist[\{show nargs}];"
                            _ <- foldlC (\i, n => do
                                    emit fc "local_arglist[\{show i}] = \{varName n};"
                                    pure (i + 1)) 0 args
                            emitAssign fc lh' "trampoline(\{cName n}(local_arglist))"
                    decreaseIndentation
                    emit fc "}"
                else
                    emitAssign fc lh "trampoline(\{cName n}(\{concat $ intersperse ", " $ map varName args}))"

cStatementsFromANF (AUnderApp fc n missing args) lh _ = do
    let nargs = length args
    emitAssign fc lh "makeClosure((Value *(*)())\{cName n}, \{show (nargs + missing)}, \{show nargs})"
    fillConstructorArgs "((Value_Closure*)\{assignToName lh})" args 0

cStatementsFromANF (AApp fc _ closure arg) lh tailPosition =
    emitAssign fc lh $ (case tailPosition of
        NotInTailPosition => "apply_closure("
        InTailPosition    => "tailcall_apply_closure(") ++ varName closure ++ ", " ++ varName arg ++ ")"

cStatementsFromANF (ALet fc var value body) lh tailPosition = do
    let var' = "var_\{show var}"
    cStatementsFromANF value (NoYetDcl var') NotInTailPosition
    registerVariableForAutomaticFreeing var'
    cStatementsFromANF body lh tailPosition

cStatementsFromANF (ACon fc n coninfo tag args) lh _ =
    -- maps a special constructor to NULL.
    if coninfo == UNIT || coninfo == NIL || coninfo == NOTHING || coninfo == ZERO
        then emitAssign fc lh "((Value*)NULL /* ACon \{show n} \{show coninfo} */)"
        else do
            emitAssign fc lh "newConstructor(\{show $ length args}, \{maybe "0" show tag} /* ACon \{show n} \{show coninfo} */)"
            let varname = "((Value_Constructor*)\{assignToName lh})"
            when (coninfo == TYCON) $ emit emptyFC "\{varname}->tyconName = \{cStringQuoted $ show n};"
            fillConstructorArgs varname args 0

cStatementsFromANF (AOp fc _ op args) lh _ = emitAssign fc lh $ cOp op $ map varName args
cStatementsFromANF (AExtPrim fc _ p args) lh _ = do
    let prims : List String =
        ["prim__newIORef", "prim__readIORef", "prim__writeIORef", "prim__newArray",
         "prim__arrayGet", "prim__arraySet", "prim__getField", "prim__setField",
         "prim__void", "prim__os", "prim__codegen", "prim__onCollect", "prim__onCollectAny" ]
    case p of
        NS _ (UN (Basic pn)) =>
           unless (elem pn prims) $ throw $ InternalError $ "INTERNAL ERROR: Unknown primitive: " ++ cName p
        _ => throw $ InternalError $ "INTERNAL ERROR: Unknown primitive: " ++ cName p
    emitAssign fc lh "idris2_\{cName p}(\{showSep ", " (map varName args)})"

-- Optimizing some special cases of ConCase
cStatementsFromANF (AConCase fc sc [] Nothing) _ _ = throw $ InternalError "[refc] AConCase : empty concase"
cStatementsFromANF (AConCase fc sc [] (Just mDef)) lh tailPosition = cStatementsFromANF mDef lh tailPosition
cStatementsFromANF (AConCase fc sc alts mDef) lh tailPosition = do
    let sc' = varName sc
    emitAssign fc lh "NULL"

    _ <- foldlC (\els, (MkAConAlt name coninfo tag args bdy) => do
        if (coninfo == NIL || coninfo == NOTHING || coninfo == ZERO || coninfo == UNIT) && null args
            then emit emptyFC "\{els}if (NULL == \{sc'} /* \{show name} \{show coninfo} */) {"
            else if coninfo == CONS || coninfo == JUST || coninfo == SUCC
            then emit emptyFC "\{els}if (NULL != \{sc'} /* \{show name} \{show coninfo} */) {"
            else if coninfo == TYCON
            then emit emptyFC "\{els}if (! strcmp(((Value_Constructor*)\{sc'})->tyconName, \{cStringQuoted $ show name})) { "
            else let Just tag' = tag | _ => throw $ InternalError "[refc] AConCase : MkConAlt has no tag. \{show name} \{show coninfo}"
                  in emit emptyFC "\{els}if (\{show tag'} == ((Value_Constructor*)\{sc'})->tag /* \{show name} \{show coninfo} */) {"
        concaseBody (assignToName lh) sc' args bdy tailPosition
        pure "} else "  ) "" alts

    case mDef of
        Nothing => pure ()
        Just body => do
            emit EmptyFC "} else {"
            concaseBody (assignToName lh) "" [] body tailPosition

    emit EmptyFC $ "}"

cStatementsFromANF (AConstCase fc sc alts def) lh tailPosition = do
    let sc' = varName sc
    emitAssign fc lh "NULL"

    case integer_switch alts of
        True => do
            let tmpint = "tmp_\{show !(getNextCounter)}"
            emit emptyFC "int \{tmpint} = extractInt(\{sc'});"
            _ <- foldlC (\els, (MkAConstAlt c body) => do
                    emit emptyFC "\{els}if (\{tmpint} == \{show $ const2Integer c 0}) {"
                    concaseBody (assignToName lh) "" [] body tailPosition
                    pure "} else ") "" alts
            pure ()
        False => do
            _ <- foldlC (\els, (MkAConstAlt c body) => do
                    case c of
                        Str x => emit emptyFC "\{els}if (! strcmp(\{cStringQuoted x}, ((Value_String*)\{sc'})->str)) {"
                        Db x  => emit emptyFC "\{els}if (((Value_Double*)\{sc'})->d == \{show x}) {"
                        x => throw $ InternalError "[refc] AConstCast : unsupported type. \{show fc} \{show x}"
                    concaseBody (assignToName lh) "" [] body tailPosition
                    pure "} else ") "" alts
            pure ()

    case def of
        Nothing => pure ()
        Just body => do
            emit EmptyFC "} else {"
            concaseBody (assignToName lh) "" [] body tailPosition

    emit EmptyFC $ "}"

cStatementsFromANF (APrimVal fc c) lh _ = emitAssign fc lh $ cConstant c
cStatementsFromANF (AErased fc)    lh _ = emitAssign fc lh "NULL"
cStatementsFromANF (ACrash fc x)   lh _ = do
  emit fc $ "fprintf(stderr, \"[refc] Crash : %s %s¥n\", \{cStringQuoted $ show fc}, \{cStringQuoted x});"
  emitAssign fc lh "(NULL /* CRASH */)"





addCommaToList : List String -> List String
addCommaToList [] = []
addCommaToList (x :: xs) = ("  " ++ x) :: map (", " ++) xs


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
    let nargs = length args
    let fn = "Value *\{cName !(getFullName n)}"
            ++ (if nargs == 0 then "(void)"
               else if nargs > MaxExtractFunArgs then "(Value *var_arglist[\{show nargs}])"
               else ("\n(\n" ++ (showSep "\n" $ addCommaToList (map (\i =>  "  Value * var_" ++ (show i)) args))) ++ "\n)")
    update FunctionDefinitions $ \otherDefs => (fn ++ ";\n") :: otherDefs
    newTemporaryVariableLevel
    emit EmptyFC fn
    emit EmptyFC "{"
    increaseIndentation
    when (nargs > MaxExtractFunArgs) $ do
        -- What a strange code, but I believe the C compiler will erase the aliasing.
        -- Please, don't create a new copy on the stack!
        _ <- foldlC (\i, j => do
           emit EmptyFC "Value *var_\{show j} = var_arglist[\{show i}];"
           pure (i + 1)) 0 args
        pure ()
    cStatementsFromANF anf (NoYetDcl "returnValue") InTailPosition
    freeTmpVars
    emit EmptyFC $ "return returnValue;"
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
          update FunctionDefinitions $ \otherDefs => (fnDef ++ "\n") :: otherDefs
          typeVarNameArgList <- createFFIArgList fargs

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

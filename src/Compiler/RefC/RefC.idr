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
import Libraries.Data.SortedMap
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
data EnvTracker : Type where
data FunctionDefinitions : Type where
data IndentLevel : Type where
data HeaderFiles : Type where

ReuseMap = SortedMap Name String
Owned = SortedSet AVar

||| Environment for precise reference counting.
||| If variable borrowed (that is, it is not in the owned set) when used, call a function newReference.
||| If variable owned, then use it directly.
||| Reuse Map contains the name of the reusable constructor and variable
record Env where
  constructor MkEnv
  owned : Owned
  reuseMap : ReuseMap

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

addHeader : {auto h : Ref HeaderFiles (SortedSet String)}
         -> String
         -> Core ()
addHeader = update HeaderFiles . insert

applyFunctionToVars : {auto oft : Ref OutfileText Output}
                    -> {auto il : Ref IndentLevel Nat}
                    -> String
                    -> List String
                    -> Core $ ()
applyFunctionToVars fun vars = traverse_ (\v => emit EmptyFC $ fun ++ "(" ++ v ++ ");" ) vars

removeVars : {auto oft : Ref OutfileText Output}
           -> {auto il : Ref IndentLevel Nat}
           -> List String
           -> Core $ ()
removeVars = applyFunctionToVars "removeReference"

dupVars : {auto oft : Ref OutfileText Output}
           -> {auto il : Ref IndentLevel Nat}
           -> List String
           -> Core $ ()
dupVars = applyFunctionToVars "newReference"

removeReuseConstructors : {auto oft : Ref OutfileText Output}
                        -> {auto il : Ref IndentLevel Nat}
                        -> List String
                        -> Core $ ()
removeReuseConstructors = applyFunctionToVars "removeReuseConstructor"

avarToC : Env -> AVar -> String
avarToC env var =
    if contains var env.owned then varName var
        -- case when the variable is borrowed
    else "newReference(" ++ varName var ++ ")"

moveFromOwnedToBorrowed : Env -> SortedSet AVar -> Env
moveFromOwnedToBorrowed env vars = { owned $= (`difference` vars) } env

makeArglist : {auto a : Ref ArgCounter Nat}
           -> {auto oft : Ref OutfileText Output}
           -> {auto il : Ref IndentLevel Nat}
           -> {auto e : Ref EnvTracker Env}
           -> Nat
           -> List AVar
           -> Core String
makeArglist missing xs = do
    c <- getNextCounter
    let arglist = "arglist_" ++ (show c)
    emit EmptyFC $  "Value_Arglist *"
                 ++ arglist
                 ++ " = newArglist(" ++ show missing
                 ++ "," ++ show (length xs + missing)
                 ++ ");"
    pushArgToArglist !(get EnvTracker) arglist xs 0
    pure arglist
where
    pushArgToArglist : Env -> String -> List AVar -> Nat -> Core ()
    pushArgToArglist _ arglist [] k = pure ()
    pushArgToArglist env arglist (arg :: args) k = do
        let ownedArg = if contains arg env.owned then singleton arg else empty
        emit EmptyFC $ arglist
                    ++ "->args[" ++ show k ++ "] = "
                    ++ avarToC env arg ++ ";"
        pushArgToArglist (moveFromOwnedToBorrowed env ownedArg) arglist args (S k)

fillConstructorArgs : {auto oft : Ref OutfileText Output}
                   -> {auto il : Ref IndentLevel Nat}
                   -> Env
                   -> String
                   -> List AVar
                   -> Nat
                   -> Core ()
fillConstructorArgs _ _ [] _ = pure ()
fillConstructorArgs env cons (v :: vars) k = do
    let ownedVars = if contains v env.owned then singleton v else empty
    emit EmptyFC $ cons ++ "->args["++ show k ++ "] = " ++ avarToC env v ++ ";"
    fillConstructorArgs (moveFromOwnedToBorrowed env ownedVars) cons vars (S k)

showTag : Maybe Int -> String
showTag Nothing = "-1"
showTag (Just i) = show i

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

||| The function takes as arguments the current ReuseMap and the constructors that will be used.
||| Returns constructor variables to remove and constructors to reuse.
dropUnusedReuseCons : ReuseMap -> SortedSet Name -> (List String, ReuseMap)
dropUnusedReuseCons reuseMap usedCons =
    -- if there is no constructor named by that name, then the reuse constructor is deleted
    let dropReuseMap = differenceMap reuseMap usedCons in
    let actualReuseMap = intersectionMap reuseMap usedCons in
    (values dropReuseMap, actualReuseMap)

||| The function takes as arguments the current owned vars and set vars that will be used.
||| Returns variables to remove and actual owned vars.
dropUnusedOwnedVars : Owned -> SortedSet AVar -> (List String, Owned)
dropUnusedOwnedVars owned usedVars =
    let actualOwned = intersection owned usedVars in
    let shouldDrop = difference owned actualOwned in
    (varName <$> SortedSet.toList shouldDrop, actualOwned)

locally : {auto t : Ref EnvTracker Env} -> Env -> Core () -> Core ()
locally newEnv act = do
    oldEnv <- get EnvTracker
    put EnvTracker newEnv
    act
    put EnvTracker oldEnv

-- if the constructor is unique use it, otherwise add it to should drop vars and create null constructor
addReuseConstructor : {auto a : Ref ArgCounter Nat}
                    -> {auto oft : Ref OutfileText Output}
                    -> {auto il : Ref IndentLevel Nat}
                    -> ReuseMap
                    -> String
                    -> Name
                    -> List String
                    -> SortedSet Name
                    -> List String
                    -> SortedMap Name String
                    -> Core (List String, SortedMap Name String)
addReuseConstructor reuseMap sc conName conArgs consts shouldDrop actualReuseConsts =
    -- to avoid conflicts, we check that there is no constructor with the same name in reuse map
    -- we also check that the constructor will be used later and that the variable will be deleted
    if (isNothing $ SortedMap.lookup conName reuseMap)
       && contains conName consts
       && (isJust $ find (== sc) shouldDrop) then do
        c <- getNextCounter
        let constr = "constructor_" ++ (show c)
        emit EmptyFC $ "Value_Constructor* " ++ constr ++ " = NULL;"
        -- If the constructor variable is unique (has 1 reference), then assign it for reuse
        emit EmptyFC $ "if (isUnique(" ++ sc ++ ")) {"
        increaseIndentation
        emit EmptyFC $ constr ++ " = (Value_Constructor*)" ++ sc ++ ";"
        decreaseIndentation
        emit EmptyFC "}"
        -- Otherwise, delete and duplicate constructor variables
        emit EmptyFC "else {"
        increaseIndentation
        -- remove dup and remove if they are executed for the same argument
        dupVars (conArgs \\ shouldDrop)
        removeVars [sc]
        decreaseIndentation
        emit EmptyFC "}"
        pure (shouldDrop \\ (sc :: conArgs), insert conName constr actualReuseConsts)
    else do
        dupVars $ conArgs \\ shouldDrop
        pure (shouldDrop \\ conArgs, actualReuseConsts)

mutual
    concaseBody : {auto a : Ref ArgCounter Nat}
                 -> {auto e : Ref EnvTracker Env}
                 -> {auto oft : Ref OutfileText Output}
                 -> {auto il : Ref IndentLevel Nat}
                 -> List String -> List String
                 -> String -> String -> List Int -> ANF -> TailPositionStatus
                 -> Core ()
    concaseBody dropVars dropReuseCons returnvar expr args bdy tailPosition = do
        increaseIndentation
        _ <- foldlC (\k, arg => do
            emit emptyFC "Value *var_\{show arg} = ((Value_Constructor*)\{expr})->args[\{show k}];"
            pure (S k) ) 0 args
        removeVars dropVars
        removeReuseConstructors dropReuseCons
        assignment <- cStatementsFromANF bdy tailPosition
        emit emptyFC "\{returnvar} = \{callByPosition tailPosition assignment};"
        decreaseIndentation

    cStatementsFromANF : {auto a : Ref ArgCounter Nat}
                      -> {auto oft : Ref OutfileText Output}
                      -> {auto il : Ref IndentLevel Nat}
                      -> {auto e : Ref EnvTracker Env}
                      -> ANF
                      -> TailPositionStatus
                      -> Core ReturnStatement
    cStatementsFromANF (AV fc x) _ = do
        let returnLine = avarToC !(get EnvTracker) x
        pure $ MkRS returnLine returnLine
    cStatementsFromANF (AAppName fc _ n args) _ = do
        emit fc $ ("// start " ++ cName n ++ "(" ++ showSep ", " (map (\v => varName v) args) ++ ")")
        arglist <- makeArglist 0 args
        c <- getNextCounter
        let f_ptr_name = "fPtr_" ++ show c
        emit fc $ "Value *(*"++ f_ptr_name ++ ")(Value_Arglist*) = " ++ cName n ++ "_arglist;"
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
    cStatementsFromANF (AApp fc _ closure arg) _ = do
        env <- get EnvTracker
        pure $ MkRS ("apply_closure(" ++ avarToC env closure ++ ", " ++ avarToC env arg ++ ")")
                    ("tailcall_apply_closure(" ++ avarToC env closure ++ ", " ++ avarToC env arg ++ ")")
    cStatementsFromANF (ALet fc var value body) tailPosition = do
        env <- get EnvTracker
        let usedVars = freeVariables body
        let borrowVal = intersection env.owned (delete (ALocal var) usedVars)
        let owned' = if contains (ALocal var) usedVars then insert (ALocal var) borrowVal else borrowVal
        let usedCons = usedConstructors value
        -- When translating value into C, we borrow variables that will be used in body
        let valueEnv = { reuseMap $= (`intersectionMap` usedCons) } (moveFromOwnedToBorrowed env borrowVal)
        put EnvTracker valueEnv
        valueAssignment <- cStatementsFromANF value NotInTailPosition
        emit fc $ "Value * var_" ++ (show var) ++ " = " ++ nonTailCall valueAssignment ++ ";"
        unless (contains (ALocal var) usedVars) $ emit fc $ "removeReference(" ++ "var_" ++ (show var) ++ ");"
        put EnvTracker ({ owned := owned', reuseMap $= (`differenceMap` usedCons) } env)
        bodyAssignment <- cStatementsFromANF body tailPosition
        pure bodyAssignment
    cStatementsFromANF (ACon fc n UNIT tag []) _ = do
        pure $ MkRS "(Value*)NULL" "(Value*)NULL"
    cStatementsFromANF (ACon fc n _ mTag args) _ = do
        env <- get EnvTracker
        let mConstr = SortedMap.lookup n $ reuseMap env
        let createNewConstructor = " = newConstructor("
                        ++ (show (length args))
                        ++ ", "  ++ showTag mTag  ++ ", "
                        ++ "\"" ++ cName n ++ "\""
                        ++ ");"
        case mConstr of
            Just constr => do
                emit fc $ "if (!" ++ constr ++ ") {"
                increaseIndentation
                emit fc $ constr ++ createNewConstructor
                decreaseIndentation
                emit fc "}"
                fillConstructorArgs env constr args 0
                pure $ MkRS ("(Value*)" ++ constr) ("(Value*)" ++ constr)
            Nothing => do
                c <- getNextCounter
                let constr = "constructor_" ++ (show c)
                emit fc $ "Value_Constructor* " ++ constr ++ createNewConstructor
                emit fc $ " // constructor " ++ cName n
                fillConstructorArgs env constr args 0
                pure $ MkRS ("(Value*)" ++ constr) ("(Value*)" ++ constr)
    cStatementsFromANF (AOp fc _ op args) _ = do
        c <- getNextCounter
        let resultVar = "primVar_" ++ (show c)
        let argsVect = map (avarToC !(get EnvTracker)) args
        emit fc $ "Value *" ++ resultVar ++ " = " ++ cOp op argsVect ++ ";"
        -- Removing arguments that apply to primitive functions
        removeVars (foldl (\acc, elem => elem :: acc) [] (map varName args))
        pure $ MkRS resultVar resultVar
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
        let sc' = varName sc
        switchReturnVar <- getNewVarThatWillNotBeFreedAtEndOfBlock
        emit fc "Value * \{switchReturnVar} = NULL;"
        env <- get EnvTracker
        _ <- foldlC (\els, (MkAConAlt name coninfo tag args body) => do
            let conArgs = ALocal <$> args
            let ownedWithArgs = union (fromList conArgs) env.owned
            let (shouldDrop, actualOwned) = dropUnusedOwnedVars ownedWithArgs (freeVariables body)
            let usedCons = usedConstructors body
            let (dropReuseCons, actualReuseMap) = dropUnusedReuseCons env.reuseMap usedCons
            case tag of
                Nothing   => emit emptyFC "\{els}if (! strcmp(((Value_Constructor *)\{sc'})->name, \{cStringQuoted $ cName name})) {"
                Just tag' => emit emptyFC "\{els}if (((Value_Constructor *)\{sc'})->tag == \{show tag'}) {"
            increaseIndentation
            _ <- foldlC (\k, arg => do
                emit emptyFC "Value *var_\{show arg} = ((Value_Constructor*)\{sc'})->args[\{show k}];"
                pure (S k) ) 0 args
            (shouldDrop, actualReuseMap) <- addReuseConstructor env.reuseMap sc' name (varName <$> conArgs) usedCons shouldDrop actualReuseMap
            removeVars shouldDrop
            removeReuseConstructors dropReuseCons
            put EnvTracker ({owned := actualOwned, reuseMap := actualReuseMap} env)
            assignment <- cStatementsFromANF body tailPosition
            emit emptyFC "\{switchReturnVar} = \{callByPosition tailPosition assignment};"
            decreaseIndentation
            pure "} else ") "" alts
        case mDef of
            Nothing => pure ()
            Just body => do
                let (shouldDrop, actualOwned) = dropUnusedOwnedVars env.owned (freeVariables body)
                let usedCons = usedConstructors body
                let (dropReuseCons, actualReuseMap) = dropUnusedReuseCons env.reuseMap usedCons
                emit emptyFC "} else {"
                put EnvTracker ({owned := actualOwned, reuseMap := actualReuseMap} env)
                concaseBody shouldDrop dropReuseCons switchReturnVar "" [] body tailPosition
        emit emptyFC "}"
        pure $ MkRS switchReturnVar switchReturnVar
    cStatementsFromANF (AConstCase fc sc alts def) tailPosition = do
        let sc' = varName sc
        switchReturnVar <- getNewVarThatWillNotBeFreedAtEndOfBlock
        emit fc "Value *\{switchReturnVar} = NULL;"
        env <- get EnvTracker
        case integer_switch alts of
            True => do
                tmpint <- getNewVarThatWillNotBeFreedAtEndOfBlock
                emit emptyFC "int \{tmpint} = extractInt(\{sc'});"
                _ <- foldlC (\els, (MkAConstAlt c body) => do
                    let (shouldDrop, actualOwned) = dropUnusedOwnedVars env.owned (freeVariables body)
                    let usedCons = usedConstructors body
                    let (dropReuseCons, actualReuseMap) = dropUnusedReuseCons env.reuseMap usedCons
                    emit emptyFC "\{els}if (\{tmpint} == \{show $ const2Integer c 0}) {"
                    put EnvTracker ({owned := actualOwned, reuseMap := actualReuseMap} env)
                    concaseBody shouldDrop dropReuseCons switchReturnVar "" [] body tailPosition
                    pure "} else ") "" alts
                pure ()

            False => do
                _ <- foldlC (\els, (MkAConstAlt c body) => do
                    let (shouldDrop, actualOwned) = dropUnusedOwnedVars env.owned (freeVariables body)
                    let usedCons = usedConstructors body
                    let (dropReuseCons, actualReuseMap) = dropUnusedReuseCons env.reuseMap usedCons
                    case c of
                        Str x => emit emptyFC "\{els}if (! strcmp(\{cStringQuoted x}, ((Value_String *)\{sc'})->str)) {"
                        Db  x => emit emptyFC "\{els}if (((Value_Double *)\{sc'})->d == \{show x}) {"
                        x => throw $ InternalError "[refc] AConstCase : unsupported type. \{show fc} \{show x}"
                    put EnvTracker ({owned := actualOwned, reuseMap := actualReuseMap} env)
                    concaseBody shouldDrop dropReuseCons switchReturnVar "" [] body tailPosition
                    pure "} else ") "" alts
                pure ()

        case def of
            Nothing => pure ()
            Just body => do
                let (shouldDrop, actualOwned) = dropUnusedOwnedVars env.owned (freeVariables body)
                let usedCons = usedConstructors body
                let (dropReuseCons, actualReuseMap) = dropUnusedReuseCons env.reuseMap usedCons
                emit emptyFC "} else {"
                put EnvTracker ({owned := actualOwned, reuseMap := actualReuseMap} env)
                concaseBody shouldDrop dropReuseCons switchReturnVar "" [] body tailPosition
        emit emptyFC "}"
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
    let argsVars = fromList $ ALocal <$> args
    let bodyFreeVars = freeVariables anf
    let shouldDrop = difference argsVars bodyFreeVars
    let argsNrs = getArgsNrList args Z
    emit EmptyFC fn
    emit EmptyFC "{"
    increaseIndentation
    removeVars (varName <$> SortedSet.toList shouldDrop)
    _ <- newRef EnvTracker (MkEnv bodyFreeVars empty)
    assignment <- cStatementsFromANF anf InTailPosition
    emit EmptyFC $ "Value *returnValue = " ++ tailCall assignment ++ ";"
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
          let removeVarsArgList = removeVars ((\(_, varName, _) => varName) <$> typeVarNameArgList)
          case ret of
              CFIORes CFUnit => do
                  emit EmptyFC $ cName fctName
                              ++ "("
                              ++ showSep ", " (map (\(_, vn, vt) => extractValue cLang vt vn) (discardLastArgument typeVarNameArgList))
                              ++ ");"
                  removeVarsArgList
                  emit EmptyFC "return NULL;"
              CFIORes ret => do
                  emit EmptyFC $ cTypeOfCFType ret ++ " retVal = " ++ cName fctName
                              ++ "("
                              ++ showSep ", " (map (\(_, vn, vt) => extractValue cLang vt vn) (discardLastArgument typeVarNameArgList))
                              ++ ");"
                  removeVarsArgList
                  emit EmptyFC $ "return (Value*)" ++ packCFType ret "retVal" ++ ";"
              _ => do
                  emit EmptyFC $ cTypeOfCFType ret ++ " retVal = " ++ cName fctName
                              ++ "("
                              ++ showSep ", " (map (\(_, vn, vt) => extractValue cLang vt vn) typeVarNameArgList)
                              ++ ");"
                  removeVarsArgList
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
    let headerFiles = SortedSet.toList !(get HeaderFiles)
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

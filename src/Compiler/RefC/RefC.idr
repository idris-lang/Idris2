module Compiler.RefC.RefC

import Compiler.RefC.CC

import Compiler.Common
import Compiler.CompileExpr
import Compiler.ANF
import Compiler.Generated

import Core.Directory

import Idris.Syntax

import Libraries.Data.DList
import Data.SortedSet
import Data.SortedMap
import Data.Vect

import System
import System.File

import Data.String
import Idris.Env

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
                  else "UINT32_C(" ++ show (ord c) ++ ")"

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
cPrimType StringType = "String"
cPrimType CharType = "Char"
cPrimType DoubleType = "Double"
cPrimType WorldType = "void"

||| Generate scheme for a primitive function.
cOp : {0 arity : Nat} -> PrimFn arity -> Vect arity String -> String
cOp (Neg ty)      [x]       = "idris2_negate_"  ++  cPrimType ty ++ "(" ++ x ++ ")"
cOp StrLength     [x]       = "stringLength(" ++ x ++ ")"
cOp StrHead       [x]       = "head(" ++ x ++ ")"
cOp StrTail       [x]       = "tail(" ++ x ++ ")"
cOp StrReverse    [x]       = "reverse(" ++ x ++ ")"
cOp (Cast i o)    [x]       = "idris2_cast_" ++ (cPrimType i) ++ "_to_" ++ (cPrimType o) ++ "(" ++ x ++ ")"
cOp DoubleExp     [x]       = "idris2_mkDouble(exp(idris2_vp_to_Double(" ++ x ++ ")))"
cOp DoubleLog     [x]       = "idris2_mkDouble(log(idris2_vp_to_Double(" ++ x ++ ")))"
cOp DoublePow     [x, y]    = "idris2_mkDouble(pow(idris2_vp_to_Double(" ++ x ++ "), idris2_vp_to_Double(" ++ y ++ ")))"
cOp DoubleSin     [x]       = "idris2_mkDouble(sin(idris2_vp_to_Double(" ++ x ++ ")))"
cOp DoubleCos     [x]       = "idris2_mkDouble(cos(idris2_vp_to_Double(" ++ x ++ ")))"
cOp DoubleTan     [x]       = "idris2_mkDouble(tan(idris2_vp_to_Double(" ++ x ++ ")))"
cOp DoubleASin    [x]       = "idris2_mkDouble(asin(idris2_vp_to_Double(" ++ x ++ ")))"
cOp DoubleACos    [x]       = "idris2_mkDouble(acos(idris2_vp_to_Double(" ++ x ++ ")))"
cOp DoubleATan    [x]       = "idris2_mkDouble(atan(idris2_vp_to_Double(" ++ x ++ ")))"
cOp DoubleSqrt    [x]       = "idris2_mkDouble(sqrt(idris2_vp_to_Double(" ++ x ++ ")))"
cOp DoubleFloor   [x]       = "idris2_mkDouble(floor(idris2_vp_to_Double(" ++ x ++ ")))"
cOp DoubleCeiling [x]       = "idris2_mkDouble(ceil(idris2_vp_to_Double(" ++ x ++ ")))"
cOp (Add ty)      [x, y]    = "idris2_add_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (Sub ty)      [x, y]    = "idris2_sub_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (Mul ty)      [x, y]    = "idris2_mul_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (Div ty)      [x, y]    = "idris2_div_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (Mod ty)      [x, y]    = "idris2_mod_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (ShiftL ty)   [x, y]    = "idris2_shiftl_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (ShiftR ty)   [x, y]    = "idris2_shiftr_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (BAnd ty)     [x, y]    = "idris2_and_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (BOr ty)      [x, y]    = "idris2_or_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (BXOr ty)     [x, y]    = "idris2_xor_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (LT ty)       [x, y]    = "idris2_lt_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (GT ty)       [x, y]    = "idris2_gt_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (EQ ty)       [x, y]    = "idris2_eq_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (LTE ty)      [x, y]    = "idris2_lte_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp (GTE ty)      [x, y]    = "idris2_gte_" ++ cPrimType ty ++ "(" ++ x ++ ", " ++ y ++ ")"
cOp StrIndex      [x, i]    = "strIndex(" ++ x ++ ", " ++ i ++ ")"
cOp StrCons       [x, y]    = "strCons(" ++ x ++ ", " ++ y ++ ")"
cOp StrAppend     [x, y]    = "strAppend(" ++ x ++ ", " ++ y ++ ")"
cOp StrSubstr     [x, y, z] = "strSubstr(" ++ x ++ ", " ++ y  ++ ", " ++ z ++ ")"
cOp BelieveMe     [_, _, x] = "idris2_newReference(" ++ x ++ ")"
cOp Crash         [_, msg]  = "idris2_crash(" ++ msg ++ ");"

varName : AVar -> String
varName (ALocal i) = "var_" ++ (show i)
varName (ANull)    = "NULL"

data ArgCounter : Type where
data EnvTracker : Type where
data FunctionDefinitions : Type where
data IndentLevel : Type where
data HeaderFiles : Type where
data StructDecls : Type where
data CallbackDecls : Type where
data ConstDef
  = CDI64 String
  | CDB64 String
  | CDDb  String
  | CDStr String

constantName : ConstDef -> String
constantName = \case
  CDI64 x => go "Int64" x
  CDB64 x => go "Bits64" x
  CDDb x  => go "Double" x
  CDStr x => go "String" x
  where go : String -> String -> String
        go x y = "idris2_constant_\{x}_\{y}"

ReuseMap = SortedMap Name String
Owned = SortedSet AVar

||| Environment for precise reference counting.
||| If variable borrowed (that is, it is not in the owned set) when used, call a function idris2_newReference.
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

getNextCounter : {auto a : Ref ArgCounter Nat} -> Core String
getNextCounter = do
    c <- get ArgCounter
    put ArgCounter (S c)
    pure $ show c

getNewVarThatWillNotBeFreedAtEndOfBlock : {auto a : Ref ArgCounter Nat} -> Core String
getNewVarThatWillNotBeFreedAtEndOfBlock = pure $ "tmp_" ++ !(getNextCounter)


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
    -- Emit a #line directive for concrete source locations (MkFC only, not virtual).
    -- This lets C compilers and debuggers (gdb/lldb) map generated C back to the
    -- original Idris source file and line.
    case fc of
        MkFC origin (startLine, _) _ =>
            update OutfileText $ flip snoc $
                "#line " ++ show (startLine + 1) ++ " " ++ cStringQuoted (show origin)
        _ => pure ()
    let comment = "// " ++ show fc
    indent <- indentation
    let indentedLine = indent ++ line
    update OutfileText $ case isLTE (length indentedLine) maxLineLengthForComment of
        (Yes _) => flip snoc (lJust indentedLine maxLineLengthForComment ' ' ++ " " ++ comment)
        (No _)  => flip appendR [indentedLine, (lJust ""   maxLineLengthForComment ' ' ++ " " ++ comment)]

applyFunctionToVars : {auto oft : Ref OutfileText Output}
                    -> {auto il : Ref IndentLevel Nat}
                    -> String
                    -> List String
                    -> Core ()
applyFunctionToVars fun vars = traverse_ (\v => emit EmptyFC $ fun ++ "(" ++ v ++ ");" ) vars

removeVars : {auto oft : Ref OutfileText Output}
           -> {auto il : Ref IndentLevel Nat}
           -> List String
           -> Core ()
removeVars = applyFunctionToVars "idris2_removeReference"

dupVars : {auto oft : Ref OutfileText Output}
           -> {auto il : Ref IndentLevel Nat}
           -> List String
           -> Core ()
dupVars = applyFunctionToVars "idris2_newReference"


removeReuseConstructors : {auto oft : Ref OutfileText Output}
                        -> {auto il : Ref IndentLevel Nat}
                        -> List String
                        -> Core ()
removeReuseConstructors = applyFunctionToVars "idris2_removeReuseConstructor"

avarToC : Env -> AVar -> String
avarToC env var =
    if contains var env.owned then varName var
        -- case when the variable is borrowed
    else "idris2_newReference(" ++ varName var ++ ")"

avarsToC : Owned -> List AVar -> List String
avarsToC _ [] = []
avarsToC owned (v::vars) =
  let v' = varName v in
      if contains v owned
          then v'::avarsToC (delete v owned) vars
          else "idris2_newReference(\{v'})"::avarsToC owned vars -- when v is borrowed

moveFromOwnedToBorrowed : Env -> SortedSet AVar -> Env
moveFromOwnedToBorrowed env vars = { owned $= (`difference` vars) } env

fillArgs : {auto oft : Ref OutfileText Output}
         -> {auto il : Ref IndentLevel Nat}
         -> Env
         -> String
         -> List AVar
         -> Nat
         -> Core ()
fillArgs _ _ [] _ = pure ()
fillArgs env arglist (v :: vars) k = do
    let ownedVars = if contains v env.owned then singleton v else empty
    emit EmptyFC $ "\{arglist}[\{show k}] = \{avarToC env v};"
    fillArgs (moveFromOwnedToBorrowed env ownedVars) arglist vars (S k)

makeClosure : {auto a : Ref ArgCounter Nat}
            -> {auto oft : Ref OutfileText Output}
            -> {auto il : Ref IndentLevel Nat}
            -> {auto e : Ref EnvTracker Env}
            -> FC
            -> Name
            -> List AVar
            -> Nat
            -> Core String
makeClosure fc n args missing = do
    let closure = "closure_\{!(getNextCounter)}"
    let nargs = length args
    emit fc "Value *\{closure} = (Value *)idris2_mkClosure((Value *(*)())\{cName n}, \{show $ nargs + missing}, \{show nargs});"
    fillArgs !(get EnvTracker) "((Value_Closure*)\{closure})->args" args 0
    pure closure

-- When changing this number, also change idris2_dispatch_closure in runtime.c.
-- Functions with arity ≤ MaxExtractFunArgs are called with individual Value*
-- arguments (FUN0…FUN16 in runtime.c), which lets the C compiler use
-- registers and inline calls.  Functions with arity > MaxExtractFunArgs use
-- the FUNStar calling convention: Value *f(Value **xs).  Both paths are
-- TCO-correct: tail calls return a fully-applied closure that the outermost
-- idris2_trampoline loop dispatches without growing the C stack.
--
-- Raising this limit requires adding corresponding FUNn typedefs and switch
-- cases to support/refc/runtime.c.  In C89 the maximum parameter count is 31;
-- C99 allows at least 127.  The current value of 16 is a practical sweet-spot.
MaxExtractFunArgs : Nat
MaxExtractFunArgs = 16

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

const2Integer : Constant -> Integer -> String
const2Integer c i =
    case c of
        (I x) => showIntMin x
        (I8 x) => "INT8_C(\{show x})"
        (I16 x) => "INT16_C(\{show x})"
        (I32 x) => "INT32_C(\{show x})"
        (I64 x) => showInt64Min x
        (BI x) => show x
        (Ch x) => escapeChar x
        (B8 x) => "UINT8_C(\{show x})"
        (B16 x) => "UINT16_C(\{show x})"
        (B32 x) => "UINT32_C(\{show x})"
        (B64 x) => "UINT64_C(\{show x})"
        _ => show i

data TailPositionStatus = InTailPosition | NotInTailPosition

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
    (varName <$> Prelude.toList shouldDrop, actualOwned)

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
        let constr = "constructor_" ++ !(getNextCounter)
        emit EmptyFC $ "Value_Constructor* " ++ constr ++ " = NULL;"
        -- If the constructor variable is unique (has 1 reference), then assign it for reuse
        emit EmptyFC $ "if (idris2_isUnique(" ++ sc ++ ")) {"
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
                 -> {auto _ : Ref ConstDef (SortedMap Constant ConstDef)}
                 -> Env
                 -> String -> String -> List Int -> ANF -> TailPositionStatus
                 -> Core ()
    concaseBody env returnvar expr args body tailPosition = do
        increaseIndentation
        _ <- foldlC (\k, arg => do
            emit emptyFC "Value *var_\{show arg} = ((Value_Constructor*)\{expr})->args[\{show k}];"
            pure (S k) ) 0 args

        let (shouldDrop, actualOwned) = dropUnusedOwnedVars env.owned (freeVariables body)
        let usedCons = usedConstructors body
        let (dropReuseCons, actualReuseMap) = dropUnusedReuseCons env.reuseMap usedCons
        put EnvTracker ({owned := actualOwned, reuseMap := actualReuseMap} env)
        removeVars shouldDrop
        removeReuseConstructors dropReuseCons
        emit emptyFC "\{returnvar} = \{!(cStatementsFromANF body tailPosition)};"
        decreaseIndentation

    cStatementsFromANF : {auto a : Ref ArgCounter Nat}
                      -> {auto oft : Ref OutfileText Output}
                      -> {auto il : Ref IndentLevel Nat}
                      -> {auto e : Ref EnvTracker Env}
                      -> {auto _ : Ref ConstDef (SortedMap Constant ConstDef)}
                      -> ANF
                      -> TailPositionStatus
                      -> Core String

    cStatementsFromANF (AV fc x) _ = pure $ avarToC !(get EnvTracker) x
    cStatementsFromANF (AAppName fc _ n args) tailPosition = do
        let nargs = length args
        case tailPosition of
            InTailPosition => makeClosure fc n args 0
            _ => if nargs > MaxExtractFunArgs
                then pure "idris2_trampoline(\{!(makeClosure fc n args 0)})"
                else do
                    env <- get EnvTracker
                    let args' = avarsToC env.owned args
                    pure "idris2_trampoline(\{cName n}(\{concat $ intersperse ", " args'}))"

    cStatementsFromANF (AUnderApp fc n missing args) _ = makeClosure fc n args missing
    cStatementsFromANF (AApp fc _ closure arg) tailPosition = do
       env <- get EnvTracker
       pure $ (case tailPosition of
           NotInTailPosition =>          "idris2_apply_closure"
           InTailPosition    => "idris2_tailcall_apply_closure") ++ "(\{avarToC env closure}, \{avarToC env arg})"

    cStatementsFromANF (ALet fc var value body) tailPosition = do
        env <- get EnvTracker
        let usedVars = freeVariables body
        let borrowVal = intersection env.owned (delete (ALocal var) usedVars)
        let owned' = if contains (ALocal var) usedVars then insert (ALocal var) borrowVal else borrowVal
        let usedCons = usedConstructors value
        -- When translating value into C, we borrow variables that will be used in body
        let valueEnv = { reuseMap $= (`intersectionMap` usedCons) } (moveFromOwnedToBorrowed env borrowVal)
        put EnvTracker valueEnv
        emit fc $ "Value * var_\{show var} = \{!(cStatementsFromANF value NotInTailPosition)};"
        unless (contains (ALocal var) usedVars) $ emit fc $ "idris2_removeReference(var_\{show var});"
        put EnvTracker ({ owned := owned', reuseMap $= (`differenceMap` usedCons) } env)
        cStatementsFromANF body tailPosition

    cStatementsFromANF (ACon fc n coninfo tag args) _ = do
        if coninfo == NIL || coninfo == NOTHING || coninfo == ZERO || coninfo == UNIT
            then pure "(NULL /* \{show n} */)"
            else do
                env <- get EnvTracker
                let createNewConstructor = " = idris2_newConstructor("
                                 ++ (show (length args))
                                 ++ ", "  ++ maybe "-1" show tag  ++ ");"

                emit fc " // constructor \{show n}"
                constr <- case SortedMap.lookup n $ reuseMap env of
                    Just constr => do
                        emit fc "if (! \{constr}) {"
                        increaseIndentation
                        emit fc $ constr ++ createNewConstructor
                        decreaseIndentation
                        emit fc "}"
                        pure constr
                    Nothing => do
                        let constr = "constructor_\{!(getNextCounter)}"
                        emit fc $ "Value_Constructor* " ++ constr ++ createNewConstructor
                        when (Nothing == tag) $ emit fc "\{constr}->name = idris2_constr_\{cName n};"
                        pure constr
                fillArgs env "\{constr}->args" args 0
                pure "(Value*)\{constr}"

    cStatementsFromANF (AOp fc _ op args) _ = do
        let resultVar = "primVar_" ++ !(getNextCounter)
        let argsVect : Env -> Vect ar AVar -> Vect ar String
            argsVect _ [] = []
            argsVect env (v :: vars) =
              let ownedVars = if contains v env.owned then singleton v else empty
              in (avarToC env v) :: argsVect (moveFromOwnedToBorrowed env ownedVars) vars

        emit fc $ "Value *" ++ resultVar ++ " = " ++ cOp op (argsVect !(get EnvTracker) args) ++ ";"
        -- Removing arguments that apply to primitive functions
        removeVars $ toList $ map varName args
        pure resultVar

    cStatementsFromANF (AExtPrim fc _ p args) _ = do
        let prims : List String =
            ["prim__newIORef", "prim__readIORef", "prim__writeIORef", "prim__newArray",
             "prim__arrayGet", "prim__arraySet", "prim__getField", "prim__setField",
             "prim__os", "prim__codegen", "prim__onCollect", "prim__onCollectAny" ]
        -- CFStruct stubs are generated without a namespace prefix, so use pn.
        -- All other primitives match the support library's fully-qualified names.
        let cfstructPrims : List String = ["prim__getField", "prim__setField"]
        pn <- case p of
            NS _ (UN (Basic pn)) =>
               if elem pn prims then pure pn
               else throw $ InternalError $ "[refc] Unknown primitive: " ++ cName p
            _ => throw $ InternalError $ "[refc] Unknown primitive: " ++ cName p
        let callName = if elem pn cfstructPrims then pn else cName p
        emit fc $ "// call to external primitive " ++ callName
        pure $ "idris2_\{callName}("++ showSep ", " (map varName args) ++")"

    cStatementsFromANF (AConCase fc sc alts mDef) tailPosition = do
        let sc' = varName sc
        switchReturnVar <- getNewVarThatWillNotBeFreedAtEndOfBlock
        emit fc "Value * \{switchReturnVar} = NULL;"
        env <- get EnvTracker
        _ <- foldlC (\els, (MkAConAlt name coninfo tag args body) => do
            let erased = coninfo == NIL || coninfo == NOTHING || coninfo == ZERO || coninfo == UNIT
            if erased then emit emptyFC "\{els}if (NULL == \{sc'} /* \{show name} \{show coninfo} */) {"
                else if coninfo == CONS || coninfo == JUST || coninfo == SUCC
                then emit emptyFC "\{els}if (NULL != \{sc'} /* \{show name} \{show coninfo} */) {"
                else do
                    case tag of
                        Nothing   => emit emptyFC "\{els}if (! strcmp(((Value_Constructor *)\{sc'})->name, idris2_constr_\{cName name})) {"
                        Just tag' => emit emptyFC "\{els}if (((Value_Constructor *)\{sc'})->tag == \{show tag'} /* \{show name} */) {"

            let conArgs = ALocal <$> args
            let ownedWithArgs = union (fromList conArgs) $ if erased then delete sc env.owned else env.owned
            let (shouldDrop, actualOwned) = dropUnusedOwnedVars ownedWithArgs (freeVariables body)
            let usedCons = usedConstructors body
            let (dropReuseCons, actualReuseMap) = dropUnusedReuseCons env.reuseMap usedCons
            increaseIndentation
            _ <- foldlC (\k, arg => do
                emit emptyFC "Value *var_\{show arg} = ((Value_Constructor*)\{sc'})->args[\{show k}];"
                pure (S k) ) 0 args
            (shouldDrop, actualReuseMap) <- addReuseConstructor env.reuseMap sc' name (varName <$> conArgs) usedCons shouldDrop actualReuseMap
            removeVars shouldDrop
            removeReuseConstructors dropReuseCons
            put EnvTracker ({owned := actualOwned, reuseMap := actualReuseMap} env)
            emit emptyFC "\{switchReturnVar} = \{!(cStatementsFromANF body tailPosition)};"
            decreaseIndentation
            pure "} else ") "" alts

        case mDef of
            Nothing => pure ()
            Just body => do
                emit emptyFC "} else {"
                concaseBody env switchReturnVar "" [] body tailPosition
        emit emptyFC "}"
        pure switchReturnVar

    cStatementsFromANF (AConstCase fc sc alts def) tailPosition = do
        let sc' = varName sc
        switchReturnVar <- getNewVarThatWillNotBeFreedAtEndOfBlock
        emit fc "Value *\{switchReturnVar} = NULL;"
        env <- get EnvTracker
        case integer_switch alts of
            True => do
                tmpint <- getNewVarThatWillNotBeFreedAtEndOfBlock
                emit emptyFC "int64_t \{tmpint} = idris2_extractInt(\{sc'});"
                _ <- foldlC (\els, (MkAConstAlt c body) => do
                    emit emptyFC "\{els}if (\{tmpint} == \{const2Integer c 0}) {"
                    concaseBody env switchReturnVar "" [] body tailPosition
                    pure "} else ") "" alts
                pure ()

            False => do
                _ <- foldlC (\els, (MkAConstAlt c body) => do
                    case c of
                        Str x => emit emptyFC "\{els}if (! strcmp(\{cStringQuoted x}, ((Value_String *)\{sc'})->str)) {"
                        Db  x => emit emptyFC "\{els}if (((Value_Double *)\{sc'})->d == \{show x}) {"
                        x => throw $ InternalError "[refc] AConstCase : unsupported type. \{show fc} \{show x}"
                    concaseBody env switchReturnVar "" [] body tailPosition
                    pure "} else ") "" alts
                pure ()

        case def of
            Nothing => pure ()
            Just body => do
                emit emptyFC "} else {"
                concaseBody env switchReturnVar "" [] body tailPosition
        emit emptyFC "}"
        pure switchReturnVar

    cStatementsFromANF (APrimVal fc (I x)) tailPosition = cStatementsFromANF (APrimVal fc (I64 $ cast x)) tailPosition
    cStatementsFromANF (APrimVal fc c) _ = do
      constdefs <- get ConstDef
      case lookup c constdefs of
           Just cdef => pure "((Value*)&\{constantName cdef})" -- the constant already booked.
           Nothing => dyngen
     where
        orStagen : ConstDef -> Core String
        orStagen cdef = do -- booking the constant to generate later
            constdefs <- get ConstDef
            put ConstDef $ insert c cdef constdefs
            pure "((Value*)&\{constantName cdef})" -- the constant already booked.
        dyngen : Core String
        dyngen = case c of
            I x => if x >= 0 && x < 100
                then pure "(Value*)(&idris2_predefined_Int64[\{show x}])"
                else orStagen $ CDI64 $ cCleanString $ show x
            I8 x  => pure "idris2_mkInt8(INT8_C(\{show x}))"
            I16 x => pure "idris2_mkInt16(INT16_C(\{show x}))"
            I32 x => pure "idris2_mkInt32(INT32_C(\{show x}))"
            I64 x => if x >= 0 && x < 100
                then pure "(Value*)(&idris2_predefined_Int64[\{show x}])"
                else orStagen $ CDI64 $ cCleanString $ show x
            BI x => if x >= 0 && x < 100
                then pure "idris2_getPredefinedInteger(\{show x})"
                else pure "idris2_mkIntegerLiteral(\"\{show x}\")"
            B8 x  => pure "idris2_mkBits8(UINT8_C(\{show x}))"
            B16 x => pure "idris2_mkBits16(UINT16_C(\{show x}))"
            B32 x => pure "idris2_mkBits32(UINT32_C(\{show x}))"
            B64 x => if x >= 0 && x < 100
               then pure "(Value*)(&idris2_predefined_Bits64[\{show x}])"
               else orStagen $ CDB64 $ show x
            Db x => orStagen $ CDDb $ cCleanString $ show x
            Ch x  => pure "idris2_mkChar(\{escapeChar x})"
            Str _ => orStagen $ CDStr !(getNextCounter)
            PrT t => pure $ cPrimType t
            WorldVal => pure "(NULL /* World */)"

    cStatementsFromANF (AErased fc) _ = pure "NULL"
    cStatementsFromANF (ACrash fc x) _ = pure "(NULL /* CRASH */)"

addCommaToList : List String -> List String
addCommaToList [] = []
addCommaToList (x :: xs) = ("  " ++ x) :: map (", " ++) xs


getArgsNrList : List ty -> Nat -> List Nat
getArgsNrList [] _ = []
getArgsNrList (x :: xs) k = k :: getArgsNrList xs (S k)


-- -------------------------------------------------------------------------
-- CFStruct descriptor code generation
-- -------------------------------------------------------------------------

||| Collect all CFStruct types reachable from a CFType.
||| The returned map is (struct_name → field_list) for every unique struct.
collectCFStructs : CFType -> SortedMap String (List (String, CFType))
collectCFStructs (CFStruct n flds) =
    let inner = foldl (\m, (_, ft) => mergeWith const m (collectCFStructs ft))
                      (the (SortedMap String (List (String, CFType))) empty) flds
    in mergeWith const (singleton n flds) inner
collectCFStructs (CFIORes t)  = collectCFStructs t
collectCFStructs (CFFun a b)  = mergeWith const (collectCFStructs a) (collectCFStructs b)
collectCFStructs _            = empty

||| Map a CFType to its IDRIS2_FIELD_* enum constant (for struct descriptors).
cFieldKind : CFType -> String
cFieldKind CFInt         = "IDRIS2_FIELD_INT"
cFieldKind CFInt8        = "IDRIS2_FIELD_INT8"
cFieldKind CFInt16       = "IDRIS2_FIELD_INT16"
cFieldKind CFInt32       = "IDRIS2_FIELD_INT32"
cFieldKind CFInt64       = "IDRIS2_FIELD_INT64"
cFieldKind CFUnsigned8   = "IDRIS2_FIELD_BITS8"
cFieldKind CFUnsigned16  = "IDRIS2_FIELD_BITS16"
cFieldKind CFUnsigned32  = "IDRIS2_FIELD_BITS32"
cFieldKind CFUnsigned64  = "IDRIS2_FIELD_BITS64"
cFieldKind CFDouble      = "IDRIS2_FIELD_DOUBLE"
cFieldKind CFChar        = "IDRIS2_FIELD_CHAR"
cFieldKind CFString      = "IDRIS2_FIELD_STRING"
cFieldKind CFPtr         = "IDRIS2_FIELD_PTR"
cFieldKind CFGCPtr       = "IDRIS2_FIELD_PTR"
cFieldKind (CFStruct _ _) = "IDRIS2_FIELD_STRUCT"
cFieldKind _             = "IDRIS2_FIELD_PTR"  -- fallback for unusual types

||| Emit the static field-descriptor array and struct-descriptor for one struct.
||| Requires that the struct header has been #include-d already (for offsetof).
emitOneStructDescriptor
    : {auto oft : Ref OutfileText Output}
   -> {auto il  : Ref IndentLevel Nat}
   -> (name   : String)
   -> (fields : List (String, CFType))
   -> Core ()
emitOneStructDescriptor name flds = do
    let fvar = "idris2_struct_fields_" ++ name
    let dvar = "idris2_struct_desc_"   ++ name
    emit EmptyFC $ "static idris2_field_t " ++ fvar ++ "[] = {"
    for_ flds $ \(fn, ft) => do
        let nested = case ft of
                       CFStruct n _ => "\"" ++ n ++ "\""
                       _            => "NULL"
        emit EmptyFC $
            "  {\"" ++ fn ++ "\","
            ++ " offsetof(" ++ name ++ ", " ++ fn ++ "),"
            ++ " " ++ cFieldKind ft ++ ","
            ++ " " ++ nested ++ "},"
    emit EmptyFC "  {NULL, 0, 0, NULL}"
    emit EmptyFC "};"
    emit EmptyFC $ "static idris2_struct_t " ++ dvar ++ " = {"
    emit EmptyFC $
        "  \"" ++ name ++ "\","
        ++ " " ++ fvar ++ ","
        ++ " " ++ show (length flds) ++ ","
        ++ " sizeof(" ++ name ++ ")"
    emit EmptyFC "};"

||| Emit all struct descriptors and a struct-registration function.
||| In whole-program mode (`modular = False`) the function is named
||| `idris2_register_all_structs` and called explicitly from `main()`.
||| In modular mode (`modular = True`) a static
||| `__attribute__((constructor))` function is emitted instead so that
||| each translation unit self-registers its structs when loaded.
emitStructCode
    : {auto oft : Ref OutfileText Output}
   -> {auto il  : Ref IndentLevel Nat}
   -> {auto sd  : Ref StructDecls (SortedMap String (List (String, CFType)))}
   -> (modular : Bool)
   -> Core ()
emitStructCode modular = do
    structs <- get StructDecls
    let decls = SortedMap.toList structs
    emit EmptyFC "// --- struct descriptors (generated) ---"
    traverse_ (uncurry emitOneStructDescriptor) decls
    let fnDecl = if modular
                   then "__attribute__((constructor)) static void idris2_register_structs(void)"
                   else "static void idris2_register_all_structs(void)"
    emit EmptyFC $ fnDecl ++ " {"
    traverse_ (\(n, _) =>
        emit EmptyFC $ "  idris2_register_struct(&idris2_struct_desc_" ++ n ++ ");")
        decls
    emit EmptyFC "}"

-- -------------------------------------------------------------------------
-- CFFun (callback) trampoline code generation
-- -------------------------------------------------------------------------

||| Flatten a nested CFFun into (argTypes, retType, hasWorld).
||| hasWorld is True when the inner return is CFIORes, meaning the closure
||| expects an extra World argument that C callers don't pass.
flattenCFFun : CFType -> (List CFType, CFType, Bool)
flattenCFFun (CFFun a b) =
    let (args, ret, hw) = flattenCFFun b
    in (a :: args, ret, hw)
flattenCFFun (CFIORes t) = ([], t, True)
flattenCFFun t           = ([], t, False)

||| Short type-name suffix used in generated trampoline identifiers.
cbSuffix : CFType -> String
cbSuffix CFUnit         = "void"
cbSuffix CFInt          = "i64"
cbSuffix CFInt8         = "i8"
cbSuffix CFInt16        = "i16"
cbSuffix CFInt32        = "i32"
cbSuffix CFInt64        = "i64"
cbSuffix CFUnsigned8    = "u8"
cbSuffix CFUnsigned16   = "u16"
cbSuffix CFUnsigned32   = "u32"
cbSuffix CFUnsigned64   = "u64"
cbSuffix CFDouble       = "f64"
cbSuffix CFChar         = "char"
cbSuffix CFString       = "str"
cbSuffix CFPtr          = "ptr"
cbSuffix CFGCPtr        = "ptr"
cbSuffix CFWorld        = "world"
cbSuffix (CFFun _ _)    = "ptr"
cbSuffix (CFIORes t)    = cbSuffix t
cbSuffix (CFStruct n _) = n
cbSuffix (CFUser n _)   = "ptr"
cbSuffix _              = "ptr"

||| Unique key for a callback signature: argSuffix1_..._argSuffixN_retSuffix.
cbKey : List CFType -> CFType -> String
cbKey args ret = fastConcat (intersperse "_" (map cbSuffix args)) ++ "_" ++ cbSuffix ret

||| Collect all CFFun signatures reachable from a CFType.
||| Returns a map from key to (args, ret, hasWorld).
collectCFFuns : CFType -> SortedMap String (List CFType, CFType, Bool)
collectCFFuns ft@(CFFun a b) =
    let (args, ret, hw) = flattenCFFun ft
        key = cbKey args ret
        inner = mergeWith (\x, _ => x) (collectCFFuns a) (collectCFFuns b)
    in mergeWith (\x, _ => x) (singleton key (args, ret, hw)) inner
collectCFFuns (CFIORes t)       = collectCFFuns t
collectCFFuns (CFStruct _ flds) =
    foldl (\m, (_, ft) => mergeWith (\x, _ => x) m (collectCFFuns ft)) empty flds
collectCFFuns _ = empty

-- -------------------------------------------------------------------------

cTypeOfCFType : CFType -> String
cTypeOfCFType CFUnit          = "void"
cTypeOfCFType CFInt           = "int64_t"
cTypeOfCFType CFInt8          = "int8_t"
cTypeOfCFType CFInt16         = "int16_t"
cTypeOfCFType CFInt32         = "int32_t"
cTypeOfCFType CFInt64         = "int64_t"
cTypeOfCFType CFUnsigned8     = "uint8_t"
cTypeOfCFType CFUnsigned16    = "uint16_t"
cTypeOfCFType CFUnsigned32    = "uint32_t"
cTypeOfCFType CFUnsigned64    = "uint64_t"
cTypeOfCFType CFString        = "char *"
cTypeOfCFType CFDouble        = "double"
cTypeOfCFType CFChar          = "int"
cTypeOfCFType CFPtr           = "void *"
cTypeOfCFType CFGCPtr         = "void *"
cTypeOfCFType CFBuffer        = "void *"
cTypeOfCFType CFWorld         = "void *"
cTypeOfCFType (CFFun x y)     = "void *"
cTypeOfCFType (CFIORes x)     = "void *"
cTypeOfCFType (CFStruct x ys) = x ++ " *"
cTypeOfCFType (CFUser x ys)   = "void *"
cTypeOfCFType n = assert_total $ idris_crash ("INTERNAL ERROR: Unknown FFI type in C backend: " ++ show n)

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
extractValue _ CFInt            varName = "(idris2_vp_to_Int64(" ++ varName ++ "))"
extractValue _ CFInt8           varName = "(idris2_vp_to_Int8(" ++ varName ++ "))"
extractValue _ CFInt16          varName = "(idris2_vp_to_Int16(" ++ varName ++ "))"
extractValue _ CFInt32          varName = "(idris2_vp_to_Int32(" ++ varName ++ "))"
extractValue _ CFInt64          varName = "(idris2_vp_to_Int64(" ++ varName ++ "))"
extractValue _ CFUnsigned8      varName = "(idris2_vp_to_Bits8(" ++ varName ++ "))"
extractValue _ CFUnsigned16     varName = "(idris2_vp_to_Bits16(" ++ varName ++ "))"
extractValue _ CFUnsigned32     varName = "(idris2_vp_to_Bits32(" ++ varName ++ "))"
extractValue _ CFUnsigned64     varName = "(idris2_vp_to_Bits64(" ++ varName ++ "))"
extractValue _ CFString         varName = "((Value_String*)" ++ varName ++ ")->str"
extractValue _ CFDouble         varName = "(idris2_vp_to_Double(" ++ varName ++ "))"
extractValue _ CFChar           varName = "(idris2_vp_to_Char(" ++ varName ++ "))"
extractValue _ CFPtr            varName = "((Value_Pointer*)" ++ varName ++ ")->p"
extractValue _ CFGCPtr          varName = "((Value_GCPointer*)" ++ varName ++ ")->p->p"
extractValue CLangC    CFBuffer varName = "((Value_Buffer*)" ++ varName ++ ")->buffer->data"
extractValue CLangRefC CFBuffer varName = "((Value_Buffer*)" ++ varName ++ ")->buffer"
extractValue _ CFWorld          _       = "(Value *)NULL"
extractValue CLangRefC (CFFun _ _) varName = "(Value_Closure *)(" ++ varName ++ ")"
extractValue _ (CFFun x y)      varName =
    let (args, ret, hw) = flattenCFFun (CFFun x y)
    in "idris2_make_cb_" ++ cbKey args ret ++ "(" ++ varName ++ ")"
extractValue c (CFIORes x)      varName = extractValue c x varName
extractValue _ (CFStruct x xs)  varName = "((Value_Pointer*)" ++ varName ++ ")->p"
-- not really total but this way this internal error does not contaminate everything else
extractValue _ (CFUser x xs)    varName = "(Value*)" ++ varName
extractValue _ n _ = assert_total $ idris_crash ("INTERNAL ERROR: Unknown FFI type in C backend: " ++ show n)

packCFType : (cfType:CFType) -> (varName:String) -> String
packCFType CFUnit          varName = "((Value *)NULL)"
packCFType CFInt           varName = "idris2_mkInt64(" ++ varName ++ ")"
packCFType CFInt8          varName = "idris2_mkInt8(" ++ varName ++ ")"
packCFType CFInt16         varName = "idris2_mkInt16(" ++ varName ++ ")"
packCFType CFInt32         varName = "idris2_mkInt32(" ++ varName ++ ")"
packCFType CFInt64         varName = "idris2_mkInt64(" ++ varName ++ ")"
packCFType CFUnsigned64    varName = "idris2_mkBits64(" ++ varName ++ ")"
packCFType CFUnsigned32    varName = "idris2_mkBits32(" ++ varName ++ ")"
packCFType CFUnsigned16    varName = "idris2_mkBits16(" ++ varName ++ ")"
packCFType CFUnsigned8     varName = "idris2_mkBits8(" ++ varName ++ ")"
packCFType CFString        varName = "idris2_mkString(" ++ varName ++ ")"
packCFType CFDouble        varName = "idris2_mkDouble(" ++ varName ++ ")"
packCFType CFChar          varName = "idris2_mkChar(" ++ varName ++ ")"
packCFType CFPtr           varName = "idris2_makePointer(" ++ varName ++ ")"
packCFType CFGCPtr         varName = "idris2_makePointer(" ++ varName ++ ")"
packCFType CFBuffer        varName = "idris2_makeBuffer(" ++ varName ++ ")"
packCFType CFWorld         _       = "(Value *)NULL"
packCFType (CFFun x y)     varName = "idris2_makePointer((void *)" ++ varName ++ ")"
packCFType (CFIORes x)     varName = packCFType x varName
packCFType (CFStruct x xs) varName = "idris2_makePointer(" ++ varName ++ ")"
packCFType (CFUser x xs)   varName = varName
packCFType n _ = assert_total $ idris_crash ("INTERNAL ERROR: Unknown FFI type in C backend: " ++ show n)

-- -------------------------------------------------------------------------
-- CFFun trampoline emitters (placed after cTypeOfCFType/extractValue/packCFType)
-- -------------------------------------------------------------------------

||| Emit the static TLS closure slot, trampoline function, and maker for one
||| callback signature.  `key` is used in all generated names.
emitOneCallback
    : {auto oft : Ref OutfileText Output}
   -> {auto il  : Ref IndentLevel Nat}
   -> (key      : String)
   -> (args     : List CFType)
   -> (ret      : CFType)
   -> (hasWorld : Bool)
   -> Core ()
emitOneCallback key args ret hasWorld = do
    let handlerFn = "idris2_cb_handler_" ++ key
    let argtypesV = "idris2_cb_argtypes_" ++ key
    let cifV      = "idris2_cb_cif_"      ++ key
    let cifReadyV = "idris2_cb_cif_ready_" ++ key
    let makerFn   = "idris2_make_cb_"     ++ key
    let isVoidRet = case ret of { CFUnit => True; CFWorld => True; _ => False }
    let retCType  = if isVoidRet then "void" else cTypeOfCFType ret
    let indexedArgs = zipWith MkPair [0 .. length args `minus` 1] args
    let n = length args
    let fpArgsStr = if null args then "void" else showSep ", " (map cTypeOfCFType args)

    emit EmptyFC "#if IDRIS2_HAS_FFI"

    -- (1) libffi handler: called by libffi when the C caller invokes the closure.
    -- _args[i] is a void* pointing to the i-th argument value.
    -- _user_data is the Idris closure pointer.
    emit EmptyFC $ "static void " ++ handlerFn
               ++ "(ffi_cif *_cif, void *_ret, void **_args, void *_user_data) {"
    emit EmptyFC "  Value *_clo = (Value *)_user_data;"
    case indexedArgs of
      [] =>
        if hasWorld
          then do
            emit EmptyFC $ "  Value *_v0 = idris2_apply_closure(idris2_newReference(_clo), NULL);"
            unless isVoidRet $
              emit EmptyFC $ "  *((" ++ retCType ++ "*)_ret) = " ++ extractResult ret "_v0" ++ ";"
          else
            unless isVoidRet $
              emit EmptyFC $ "  *((" ++ retCType ++ "*)_ret) = " ++ extractResult ret
                "idris2_apply_closure(idris2_newReference(_clo), NULL)" ++ ";"
      ((i0, t0) :: rest) => do
        emit EmptyFC $ "  Value *_v0 = idris2_apply_closure(idris2_newReference(_clo), "
                     ++ packFromPtr t0 0 ++ ");"
        _ <- foldlC (\_, (i, t) => do
                emit EmptyFC $ "  Value *_v" ++ show i ++ " = idris2_apply_closure(_v"
                             ++ show (minus i 1) ++ ", " ++ packFromPtr t i ++ ");"
                pure ()
              ) () rest
        let lastV = "_v" ++ show (minus n 1)
        if hasWorld
          then do
            emit EmptyFC $ "  Value *_vw = idris2_apply_closure(" ++ lastV ++ ", NULL);"
            unless isVoidRet $
              emit EmptyFC $ "  *((" ++ retCType ++ "*)_ret) = " ++ extractResult ret "_vw" ++ ";"
          else
            unless isVoidRet $
              emit EmptyFC $ "  *((" ++ retCType ++ "*)_ret) = " ++ extractResult ret lastV ++ ";"
    emit EmptyFC "}"

    -- (2) Static libffi CIF for this signature (initialised once, then reused).
    let ffiArgtypes = map ffiType args
    emit EmptyFC $ "static ffi_type *" ++ argtypesV ++ "[] = {"
                ++ showSep ", " ffiArgtypes ++ ", NULL};"
    emit EmptyFC $ "static ffi_cif " ++ cifV ++ ";"
    emit EmptyFC $ "static int "     ++ cifReadyV ++ " = 0;"

    -- (3) Maker: allocate a libffi closure per-call so re-entrant callbacks
    -- each get their own function pointer and capture their own closure.
    emit EmptyFC $ "static " ++ retCType ++ " (*" ++ makerFn ++ "(Value *_clo))(" ++ fpArgsStr ++ ") {"
    emit EmptyFC $ "  if (!" ++ cifReadyV ++ ") {"
    emit EmptyFC $ "    ffi_prep_cif(&" ++ cifV ++ ", FFI_DEFAULT_ABI, " ++ show n ++ ","
    emit EmptyFC $ "                 " ++ ffiType ret ++ ", " ++ argtypesV ++ ");"
    emit EmptyFC $ "    " ++ cifReadyV ++ " = 1;"
    emit EmptyFC   "  }"
    emit EmptyFC   "  ffi_closure *_fc;"
    emit EmptyFC   "  void *_fn_ptr;"
    emit EmptyFC   "  _fc = ffi_closure_alloc(sizeof(ffi_closure), &_fn_ptr);"
    emit EmptyFC $ "  ffi_prep_closure_loc(_fc, &" ++ cifV ++ ", " ++ handlerFn ++ ", _clo, _fn_ptr);"
    emit EmptyFC $ "  return (" ++ retCType ++ " (*)(" ++ fpArgsStr ++ "))_fn_ptr;"
    emit EmptyFC   "}"

    emit EmptyFC "#else"

    -- Fallback: libffi is not available.  The maker compiles fine but aborts at
    -- runtime if a CFFun callback is actually invoked.  Programs that only use
    -- "RefC:" bindings (which pass Value_Closure* directly) are unaffected.
    emit EmptyFC $ "static " ++ retCType ++ " (*" ++ makerFn ++ "(Value *_clo))(" ++ fpArgsStr ++ ") {"
    emit EmptyFC   "  (void)_clo;"
    emit EmptyFC   "  idris2_missing_ffi();"
    emit EmptyFC   "  return NULL;"
    emit EmptyFC   "}"

    emit EmptyFC "#endif"
  where
    -- Pack a C arg (passed as void* in libffi) into a Value*
    packFromPtr : CFType -> Nat -> String
    packFromPtr CFInt        i = "idris2_mkInt64(*(int64_t *)_args["  ++ show i ++ "])"
    packFromPtr CFInt8       i = "idris2_mkInt8(*(int8_t *)_args["    ++ show i ++ "])"
    packFromPtr CFInt16      i = "idris2_mkInt16(*(int16_t *)_args["  ++ show i ++ "])"
    packFromPtr CFInt32      i = "idris2_mkInt32(*(int32_t *)_args["  ++ show i ++ "])"
    packFromPtr CFInt64      i = "idris2_mkInt64(*(int64_t *)_args["  ++ show i ++ "])"
    packFromPtr CFUnsigned8  i = "idris2_mkBits8(*(uint8_t *)_args["  ++ show i ++ "])"
    packFromPtr CFUnsigned16 i = "idris2_mkBits16(*(uint16_t *)_args[" ++ show i ++ "])"
    packFromPtr CFUnsigned32 i = "idris2_mkBits32(*(uint32_t *)_args[" ++ show i ++ "])"
    packFromPtr CFUnsigned64 i = "idris2_mkBits64(*(uint64_t *)_args[" ++ show i ++ "])"
    packFromPtr CFDouble     i = "idris2_mkDouble(*(double *)_args["   ++ show i ++ "])"
    packFromPtr CFChar       i = "idris2_mkChar(*(int *)_args["        ++ show i ++ "])"
    packFromPtr CFString     i = "idris2_mkString(*(char **)_args["    ++ show i ++ "])"
    packFromPtr CFPtr        i = "idris2_makePointer(*(void **)_args["  ++ show i ++ "])"
    packFromPtr CFGCPtr      i = "idris2_makePointer(*(void **)_args["  ++ show i ++ "])"
    packFromPtr _            i = "(Value *)*(void **)_args["            ++ show i ++ "]"

    extractResult : CFType -> String -> String
    extractResult CFInt        v = "idris2_vp_to_Int64("  ++ v ++ ")"
    extractResult CFInt8       v = "idris2_vp_to_Int8("   ++ v ++ ")"
    extractResult CFInt16      v = "idris2_vp_to_Int16("  ++ v ++ ")"
    extractResult CFInt32      v = "idris2_vp_to_Int32("  ++ v ++ ")"
    extractResult CFInt64      v = "idris2_vp_to_Int64("  ++ v ++ ")"
    extractResult CFUnsigned8  v = "idris2_vp_to_Bits8("  ++ v ++ ")"
    extractResult CFUnsigned16 v = "idris2_vp_to_Bits16(" ++ v ++ ")"
    extractResult CFUnsigned32 v = "idris2_vp_to_Bits32(" ++ v ++ ")"
    extractResult CFUnsigned64 v = "idris2_vp_to_Bits64(" ++ v ++ ")"
    extractResult CFDouble     v = "idris2_vp_to_Double(" ++ v ++ ")"
    extractResult CFChar       v = "idris2_vp_to_Char("   ++ v ++ ")"
    extractResult CFPtr        v = "((Value_Pointer *)"   ++ v ++ ")->p"
    extractResult _            v = "(intptr_t)"           ++ v

    -- Map CFType to the libffi ffi_type pointer expression
    ffiType : CFType -> String
    ffiType CFUnit        = "&ffi_type_void"
    ffiType CFInt         = "&ffi_type_sint64"
    ffiType CFInt8        = "&ffi_type_sint8"
    ffiType CFInt16       = "&ffi_type_sint16"
    ffiType CFInt32       = "&ffi_type_sint32"
    ffiType CFInt64       = "&ffi_type_sint64"
    ffiType CFUnsigned8   = "&ffi_type_uint8"
    ffiType CFUnsigned16  = "&ffi_type_uint16"
    ffiType CFUnsigned32  = "&ffi_type_uint32"
    ffiType CFUnsigned64  = "&ffi_type_uint64"
    ffiType CFDouble      = "&ffi_type_double"
    ffiType CFChar        = "&ffi_type_sint32"
    ffiType CFWorld       = "&ffi_type_void"
    ffiType _             = "&ffi_type_pointer"

||| Emit all callback trampolines and add their forward declarations to the
||| FunctionDefinitions header so callers see the declaration before the body.
emitCallbackCode
    : {auto oft : Ref OutfileText Output}
   -> {auto il  : Ref IndentLevel Nat}
   -> {auto h   : Ref HeaderFiles (SortedSet String)}
   -> {auto f   : Ref FunctionDefinitions (List String)}
   -> {auto cb  : Ref CallbackDecls (SortedMap String (List CFType, CFType, Bool))}
   -> Core ()
emitCallbackCode = do
    entries <- SortedMap.toList <$> get CallbackDecls
    unless (null entries) $ do
        -- ffi.h location varies by platform; emit a portable include block
        -- into the function-definitions preamble rather than using HeaderFiles.
        -- (HeaderFiles always wraps entries in <...> which may miss ffi/ffi.h)
        update FunctionDefinitions $ \ds =>
            "#if __has_include(<ffi.h>)\n#include <ffi.h>\n#define IDRIS2_HAS_FFI 1\n#elif __has_include(<ffi/ffi.h>)\n#include <ffi/ffi.h>\n#define IDRIS2_HAS_FFI 1\n#else\n#define IDRIS2_HAS_FFI 0\n#endif\n" :: ds
        emit EmptyFC "// --- callback trampolines (requires libffi when IDRIS2_HAS_FFI=1, stubs otherwise) ---"
        traverse_ (\(key, (args, ret, hw)) => do
            -- Forward-declare the maker so FFI wrappers (emitted before the trampolines)
            -- can call it without an implicit declaration.
            let isVoidRet = case ret of { CFUnit => True; CFWorld => True; _ => False }
            let retCType  = if isVoidRet then "void" else cTypeOfCFType ret
            let fpArgsStr = if null args then "void" else showSep ", " (map cTypeOfCFType args)
            let makerFn   = "idris2_make_cb_" ++ key
            let fwdDecl = "static " ++ retCType ++ " (*" ++ makerFn ++ "(Value *))(" ++ fpArgsStr ++ ");\n"
            update FunctionDefinitions (fwdDecl ::)
            emitOneCallback key args ret hw
          ) entries

discardLastArgument : List ty -> List ty
discardLastArgument [] = []
discardLastArgument xs@(_ :: _) = init xs

-- Emit just the static `_refc_unimplemented` helper function (used in the
-- `_ =>` fallback case where the full Value*-wrapper is emitted separately).
additionalFFIHelper : Name -> List CFType -> CFType -> String
additionalFFIHelper name argTypes (CFIORes retType) = additionalFFIHelper name (discardLastArgument argTypes) retType
additionalFFIHelper name argTypes retType =
    -- Give each parameter a name (_p0, _p1, …) so the definition is valid C99.
    let params = map (\(i, t) => cTypeOfCFType t ++ " _p" ++ show i)
                     (zipWith MkPair [0 .. length argTypes `minus` 1] argTypes)
    in "static " ++ cTypeOfCFType retType ++
       " " ++ cName name ++ "_refc_unimplemented(" ++
       (concat $ intersperse ", " params) ++ ") {\n" ++
       "  fprintf(stderr, \"ERROR: FFI function not implemented for the RefC backend:\\n" ++
       "  %s\\n(Add a \\\"C:\\\" or \\\"RefC:\\\" %%foreign binding.)\\n\", \"" ++
       show name ++ "\");\n" ++
       "  exit(1);\n}\n"

-- Emit the static helper plus a function pointer that can be called by name
-- (used for non-standard FFI langs like "scheme:" where the generated wrapper
-- calls `cName fctName` directly).
additionalFFIStub : Name -> List CFType -> CFType -> String
additionalFFIStub name argTypes (CFIORes retType) = additionalFFIStub name (discardLastArgument argTypes) retType
additionalFFIStub name argTypes retType =
    additionalFFIHelper name argTypes retType ++
    cTypeOfCFType retType ++
    " (*" ++ cName name ++ ")(" ++
    (concat $ intersperse ", " $ map cTypeOfCFType argTypes) ++ ") = (void*)" ++ cName name ++ "_refc_unimplemented;\n"

createCFunctions : {auto c : Ref Ctxt Defs}
                -> {auto a : Ref ArgCounter Nat}
                -> {auto _ : Ref ConstDef (SortedMap Constant ConstDef)}
                -> {auto f : Ref FunctionDefinitions (List String)}
                -> {auto oft : Ref OutfileText Output}
                -> {auto il : Ref IndentLevel Nat}
                -> {auto h : Ref HeaderFiles (SortedSet String)}
                -> {auto sd : Ref StructDecls (SortedMap String (List (String, CFType)))}
                -> {auto cb : Ref CallbackDecls (SortedMap String (List CFType, CFType, Bool))}
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

    let argsVars = fromList $ ALocal <$> args
    let bodyFreeVars = freeVariables anf
    let shouldDrop = difference argsVars bodyFreeVars
    let argsNrs = getArgsNrList args Z
    emit EmptyFC fn
    emit EmptyFC "{"
    increaseIndentation
    when (nargs > MaxExtractFunArgs) $ do
      _ <- foldlC (\i, j => do
         emit EmptyFC "Value *var_\{show j} = var_arglist[\{show i}];"
         pure $ i + 1) 0 args
      pure ()
    removeVars (varName <$> Prelude.toList shouldDrop)
    _ <- newRef EnvTracker (MkEnv bodyFreeVars empty)
    emit EmptyFC $ "return \{!(cStatementsFromANF anf InTailPosition)};"
    decreaseIndentation
    emit EmptyFC  "}\n"
    emit EmptyFC  ""
    pure ()


createCFunctions n (MkACon Nothing _ _) = do
  let n' = cName n
  update FunctionDefinitions $ \otherDefs => "char const idris2_constr_\{n'}[];" :: otherDefs
  emit EmptyFC "char const idris2_constr_\{n'}[] = \{cStringQuoted $ show n};"
  pure ()

createCFunctions n (MkACon tag arity nt) = do
  emit EmptyFC $ ( "// \{show n} Constructor tag " ++ show tag ++ " arity " ++ show arity) -- Nothing to compile here


createCFunctions n (MkAForeign ccs fargs ret) = do
  -- Collect CFStruct types for struct descriptor codegen (always).
  let allStructs = foldl (\m, ft => mergeWith const m (collectCFStructs ft))
                         empty (ret :: fargs)
  update StructDecls (mergeWith const allStructs)
  -- Collect CFFun types for libffi trampolines only for "C:" bindings.
  -- "RefC:" bindings receive Value_Closure* directly and don't need libffi.
  let isRefCBinding = case parseCC (additionalFFILangs ++ ["RefC", "C"]) ccs of
        Just ("RefC", _) => True
        _                => False
  unless isRefCBinding $ do
    let allCbs = foldl (\m, ft => mergeWith (\x, _ => x) m (collectCFFuns ft))
                       empty (ret :: fargs)
    update CallbackDecls (mergeWith (\x, _ => x) allCbs)

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
                      [lib, header] => update HeaderFiles $ insert header
                      -- "C:funcname, header.h" — one field, treat as header if it ends in ".h"
                      [h] => when (isSuffixOf ".h" h) $ update HeaderFiles $ insert h
                      _ => pure ()
             else emit EmptyFC $ additionalFFIStub fctName fargs ret
          let fnDef = "Value *" ++ (cName n) ++ "(" ++ showSep ", " (replicate (length fargs) "Value *") ++ ");"
          update FunctionDefinitions $ \otherDefs => (fnDef ++ "\n") :: otherDefs
          typeVarNameArgList <- createFFIArgList fargs

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
      _ => do
          -- No C/RefC binding found. Emit a named stub so that if the function
          -- is called at runtime the error names the Idris function rather than
          -- printing a generic "missing FFI" message.
          -- Use additionalFFIHelper (not additionalFFIStub) to avoid emitting a
          -- function pointer that would conflict with the Value* forward declaration.
          emit EmptyFC $ additionalFFIHelper n fargs ret
          let fnDef = "Value *" ++ (cName n) ++ "(" ++ showSep ", " (replicate (length fargs) "Value *") ++ ");"
          update FunctionDefinitions $ \otherDefs => (fnDef ++ "\n") :: otherDefs
          typeVarNameArgList <- createFFIArgList fargs
          emitFDef n typeVarNameArgList
          emit EmptyFC "{"
          increaseIndentation
          emit EmptyFC $ cName n ++ "_refc_unimplemented(" ++
                         showSep ", " (map (\(_, vn, vt) => extractValue CLangC vt vn)
                                           (discardLastArgument typeVarNameArgList)) ++ ");"
          emit EmptyFC "return NULL;"
          decreaseIndentation
          emit EmptyFC "}"

createCFunctions n (MkAError exp) = throw $ InternalError "[refc] Error with expression: \{show exp}"
-- not really total but this way this internal error does not contaminate everything else


header : {auto f : Ref FunctionDefinitions (List String)}
      -> {auto o : Ref OutfileText Output}
      -> {auto il : Ref IndentLevel Nat}
      -> {auto h : Ref HeaderFiles (SortedSet String)}
      -> {auto _ : Ref ConstDef (SortedMap Constant ConstDef)}
      -> Core ()
header = do
    let initLines = """
      #include <runtime.h>
      /* \{ generatedString "RefC" } */

      """
    let headerFiles = Prelude.toList !(get HeaderFiles)
    fns <- get FunctionDefinitions
    update OutfileText $ appendL $
        [initLines] ++
        map (\h => "#include <\{h}>\n") headerFiles ++
        ["\n// function definitions"] ++
        fns ++
        ["\n// constant value definitions"] ++
        map (uncurry genConstant) (SortedMap.toList !(get ConstDef))
  where
    go : ConstDef -> String -> String -> String -> String
    go cdef ty tag v =
      "static Value_\{ty} const \{constantName cdef}"
        ++ " = { IDRIS2_STOCKVAL(\{tag}_TAG), \{v} };"
    genConstant : Constant -> ConstDef -> String
    genConstant c cdef = case c of
      I x   => go cdef "Int64" "INT64" (showIntMin x)
      I64 x => go cdef "Int64" "INT64" (showInt64Min x)
      B64 x => go cdef "Bits64" "BITS64" "UINT64_C(\{show x})"
      Db x  => go cdef "Double" "DOUBLE" (show x)
      Str x => go cdef "String" "STRING" (cStringQuoted x)
      _ => "/* bad constant */"





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
          idris2_register_all_structs();
          Value *mainExprVal = __mainExpression_0();
          idris2_trampoline(mainExprVal);
          idris2_collectCycles();
          return 0; // bye bye
      }
      """

export
generateCSourceFile : {auto c : Ref Ctxt Defs}
                   -> {default [] additionalFFILangs : List String}
                   -> {default True withMain : Bool}
                   -> List (Name, ANFDef)
                   -> (outn : String)
                   -> Core ()
generateCSourceFile defs outn =
  do _ <- newRef ArgCounter 0
     _ <- newRef FunctionDefinitions []
     _ <- newRef ConstDef Data.SortedMap.empty
     _ <- newRef OutfileText DList.Nil
     _ <- newRef HeaderFiles empty
     _ <- newRef IndentLevel 0
     _ <- newRef StructDecls (the (SortedMap String (List (String, CFType))) empty)
     _ <- newRef CallbackDecls (the (SortedMap String (List CFType, CFType, Bool)) empty)
     traverse_ (uncurry $ createCFunctions {additionalFFILangs}) defs
     emitCallbackCode
     emitStructCode (not withMain) -- modular = True when no main, False for whole-program
     header -- added after the definition traversal in order to add all encountered function defintions
     when withMain footer
     fileContent <- get OutfileText
     let code = fastConcat (map (++ "\n") (reify fileContent))

     coreLift_ $ writeFile outn code
     log "compiler.refc" 10 $ "Generated C file " ++ outn

compileExprWhole : Ref Ctxt Defs
                -> Ref Syn SyntaxInfo
                -> (outputDir : String)
                -> ClosedTerm
                -> (outfile : String)
                -> Core (Maybe String)
compileExprWhole c s outputDir tm outfile = do
    let outn   = outputDir </> outfile ++ ".c"
    let outobj = outputDir </> outfile ++ ".o"
    let outexec = outputDir </> outfile
    coreLift_ $ mkdirAll outputDir
    cdata <- getCompileData False ANF tm
    let defs = anf cdata
    generateCSourceFile defs outn
    Just _ <- compileCObjectFile outn outobj
      | Nothing => pure Nothing
    compileCFile outobj outexec

||| Incremental-link entry point: link all pre-compiled module .o files
||| together with a generated main-only stub.
compileExprInc : Ref Ctxt Defs
              -> Ref Syn SyntaxInfo
              -> (outputDir : String)
              -> ClosedTerm
              -> (outfile : String)
              -> Core (Maybe String)
compileExprInc c s outputDir tm outfile = do
    defs <- get Ctxt
    case lookup RefC (allIncData defs) of
      Nothing => do
        coreLift $ putStrLn "Missing incremental compile data for refc, reverting to whole program compilation"
        compileExprWhole c s outputDir tm outfile
      Just (mods, _) => do
        -- Generate a tiny main-only C file that calls into the pre-compiled modules.
        let mainCFile = outputDir </> outfile ++ "__main.c"
        let mainOFile = outputDir </> outfile ++ "__main.o"
        let outexec   = outputDir </> outfile
        coreLift_ $ mkdirAll outputDir
        let mainCode = """
              #include <runtime.h>
              #include <idris_support.h>
              /* \{ generatedString "RefC" } (incremental main) */

              // main function
              int main(int argc, char *argv[])
              {
                  idris2_setArgs(argc, argv);
                  Value *mainExprVal = __mainExpression_0();
                  idris2_trampoline(mainExprVal);
                  idris2_collectCycles();
                  return 0;
              }
              """
        Right () <- coreLift $ writeFile mainCFile mainCode
          | Left err => throw (FileErr mainCFile err)
        Just _ <- compileCObjectFile mainCFile mainOFile
          | Nothing => pure Nothing
        compileCFileInc (mainOFile :: mods) outexec

||| Compile a single Idris source module to a C object file (.o) for
||| later incremental linking.  No `main()` is emitted; structs
||| self-register via `__attribute__((constructor))`.
incCompile : Ref Ctxt Defs
          -> Ref Syn SyntaxInfo
          -> (sourceFile : String)
          -> Core (Maybe (String, List String))
incCompile c s sourceFile = do
    cFile <- getTTCFileName sourceFile "c"
    oFile <- getTTCFileName sourceFile "o"
    cdata <- getIncCompileData False ANF
    let defs = anf cdata
    generateCSourceFile {withMain = False} defs cFile
    Just _ <- compileCObjectFile cFile oFile
      | Nothing => pure Nothing
    pure (Just (oFile, []))

export
compileExpr : UsePhase
           -> Ref Ctxt Defs
           -> Ref Syn SyntaxInfo
           -> (tmpDir : String)
           -> (outputDir : String)
           -> ClosedTerm
           -> (outfile : String)
           -> Core (Maybe String)
compileExpr ANF c s _ outputDir tm outfile = do
    sesh <- getSession
    if not (wholeProgram sesh) && (RefC `elem` incrementalCGs sesh)
       then compileExprInc c s outputDir tm outfile
       else do
         -- Warn when the user requested refc incremental builds but the CG
         -- was removed from incrementalCGs (most likely because the standard
         -- libraries have not yet been compiled with IDRIS2_INC_CGS=refc).
         mInc <- coreLift $ idrisGetEnv "IDRIS2_INC_CGS"
         let requestedInc = maybe False (isInfixOf "refc") mInc
         when (requestedInc && not (wholeProgram sesh)) $
           coreLift $ putStrLn $
             "Note [refc]: incremental compilation requested but not active. " ++
             "The standard libraries must be compiled with IDRIS2_INC_CGS=refc " ++
             "before per-module .o files can be used (run: make libs IDRIS2_INC_CGS=refc)."
         compileExprWhole c s outputDir tm outfile

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
codegenRefC = MkCG (compileExpr ANF) executeExpr (Just incCompile) (Just "o")

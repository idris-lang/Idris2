module Compiler.Scheme.Common

import Compiler.Common
import Compiler.CompileExpr
import Compiler.Inline

import Core.Context
import Core.Name
import Core.TT

import Libraries.Data.Bool.Extra
import Data.List
import Data.Vect

import System.Info

%default covering

export
firstExists : List String -> IO (Maybe String)
firstExists [] = pure Nothing
firstExists (x :: xs) = if !(exists x) then pure (Just x) else firstExists xs

schString : String -> String
schString s = concatMap okchar (unpack s)
  where
    okchar : Char -> String
    okchar c = if isAlphaNum c || c =='_'
                  then cast c
                  else "C-" ++ show (cast {to=Int} c)

export
schName : Name -> String
schName (NS ns n) = schString (showNSWithSep "-" ns) ++ "-" ++ schName n
schName (UN n) = schString n
schName (MN n i) = schString n ++ "-" ++ show i
schName (PV n d) = "pat--" ++ schName n
schName (DN _ n) = schName n
schName (RF n) = "rf--" ++ schString n
schName (Nested (i, x) n) = "n--" ++ show i ++ "-" ++ show x ++ "-" ++ schName n
schName (CaseBlock x y) = "case--" ++ schString x ++ "-" ++ show y
schName (WithBlock x y) = "with--" ++ schString x ++ "-" ++ show y
schName (Resolved i) = "fn--" ++ show i

export
schConstructor : (String -> String) -> Name -> Maybe Int -> List String -> String
schConstructor _ _ (Just t) args
    = "(vector " ++ show t ++ " " ++ showSep " " args ++ ")"
schConstructor schString n Nothing args
    = "(vector " ++ schString (show n) ++ " " ++ showSep " " args ++ ")"

||| Generate scheme for a plain function.
op : String -> List String -> String
op o args = "(" ++ o ++ " " ++ showSep " " args ++ ")"

||| Generate scheme for a boolean operation.
boolop : String -> List String -> String
boolop o args = "(or (and " ++ op o args ++ " 1) 0)"

||| Generate scheme for a primitive function.
schOp : PrimFn arity -> Vect arity String -> String
schOp (Add IntType) [x, y] = op "b+" [x, y, "63"]
schOp (Sub IntType) [x, y] = op "b-" [x, y, "63"]
schOp (Mul IntType) [x, y] = op "b*" [x, y, "63"]
schOp (Div IntType) [x, y] = op "b/" [x, y, "63"]
schOp (Add Bits8Type) [x, y] = op "b+" [x, y, "8"]
schOp (Sub Bits8Type) [x, y] = op "b-" [x, y, "8"]
schOp (Mul Bits8Type) [x, y] = op "b*" [x, y, "8"]
schOp (Div Bits8Type) [x, y] = op "b/" [x, y, "8"]
schOp (Add Bits16Type) [x, y] = op "b+" [x, y, "16"]
schOp (Sub Bits16Type) [x, y] = op "b-" [x, y, "16"]
schOp (Mul Bits16Type) [x, y] = op "b*" [x, y, "16"]
schOp (Div Bits16Type) [x, y] = op "b/" [x, y, "16"]
schOp (Add Bits32Type) [x, y] = op "b+" [x, y, "32"]
schOp (Sub Bits32Type) [x, y] = op "b-" [x, y, "32"]
schOp (Mul Bits32Type) [x, y] = op "b*" [x, y, "32"]
schOp (Div Bits32Type) [x, y] = op "b/" [x, y, "32"]
schOp (Add Bits64Type) [x, y] = op "b+" [x, y, "64"]
schOp (Sub Bits64Type) [x, y] = op "b-" [x, y, "64"]
schOp (Mul Bits64Type) [x, y] = op "b*" [x, y, "64"]
schOp (Div Bits64Type) [x, y] = op "b/" [x, y, "64"]
schOp (Add ty) [x, y] = op "+" [x, y]
schOp (Sub ty) [x, y] = op "-" [x, y]
schOp (Mul ty) [x, y] = op "*" [x, y]
schOp (Div IntegerType) [x, y] = op "quotient" [x, y]
schOp (Div ty) [x, y] = op "/" [x, y]
schOp (Mod ty) [x, y] = op "remainder" [x, y]
schOp (Neg ty) [x] = op "-" [x]
schOp (ShiftL IntType) [x, y] = op "blodwen-bits-shl-signed" [x, y, "63"]
schOp (ShiftL Bits8Type) [x, y] = op "blodwen-bits-shl" [x, y, "8"]
schOp (ShiftL Bits16Type) [x, y] = op "blodwen-bits-shl" [x, y, "16"]
schOp (ShiftL Bits32Type) [x, y] = op "blodwen-bits-shl" [x, y, "32"]
schOp (ShiftL Bits64Type) [x, y] = op "blodwen-bits-shl" [x, y, "64"]
schOp (ShiftL ty) [x, y] = op "blodwen-shl" [x, y]
schOp (ShiftR ty) [x, y] = op "blodwen-shr" [x, y]
schOp (BAnd ty) [x, y] = op "blodwen-and" [x, y]
schOp (BOr ty) [x, y] = op "blodwen-or" [x, y]
schOp (BXOr ty) [x, y] = op "blodwen-xor" [x, y]
schOp (LT CharType) [x, y] = boolop "char<?" [x, y]
schOp (LTE CharType) [x, y] = boolop "char<=?" [x, y]
schOp (EQ CharType) [x, y] = boolop "char=?" [x, y]
schOp (GTE CharType) [x, y] = boolop "char>=?" [x, y]
schOp (GT CharType) [x, y] = boolop "char>?" [x, y]
schOp (LT StringType) [x, y] = boolop "string<?" [x, y]
schOp (LTE StringType) [x, y] = boolop "string<=?" [x, y]
schOp (EQ StringType) [x, y] = boolop "string=?" [x, y]
schOp (GTE StringType) [x, y] = boolop "string>=?" [x, y]
schOp (GT StringType) [x, y] = boolop "string>?" [x, y]
schOp (LT ty) [x, y] = boolop "<" [x, y]
schOp (LTE ty) [x, y] = boolop "<=" [x, y]
schOp (EQ ty) [x, y] = boolop "=" [x, y]
schOp (GTE ty) [x, y] = boolop ">=" [x, y]
schOp (GT ty) [x, y] = boolop ">" [x, y]
schOp StrLength [x] = op "string-length" [x]
schOp StrHead [x] = op "string-ref" [x, "0"]
schOp StrTail [x] = op "substring" [x, "1", op "string-length" [x]]
schOp StrIndex [x, i] = op "string-ref" [x, i]
schOp StrCons [x, y] = op "string-cons" [x, y]
schOp StrAppend [x, y] = op "string-append" [x, y]
schOp StrReverse [x] = op "string-reverse" [x]
schOp StrSubstr [x, y, z] = op "string-substr" [x, y, z]

-- `e` is Euler's number, which approximates to: 2.718281828459045
schOp DoubleExp [x] = op "flexp" [x] -- Base is `e`. Same as: `pow(e, x)`
schOp DoubleLog [x] = op "fllog" [x] -- Base is `e`.
schOp DoubleSin [x] = op "flsin" [x]
schOp DoubleCos [x] = op "flcos" [x]
schOp DoubleTan [x] = op "fltan" [x]
schOp DoubleASin [x] = op "flasin" [x]
schOp DoubleACos [x] = op "flacos" [x]
schOp DoubleATan [x] = op "flatan" [x]
schOp DoubleSqrt [x] = op "flsqrt" [x]
schOp DoubleFloor [x] = op "flfloor" [x]
schOp DoubleCeiling [x] = op "flceiling" [x]

schOp (Cast IntType StringType) [x] = op "number->string" [x]
schOp (Cast IntegerType StringType) [x] = op "number->string" [x]
schOp (Cast Bits8Type StringType) [x] = op "number->string" [x]
schOp (Cast Bits16Type StringType) [x] = op "number->string" [x]
schOp (Cast Bits32Type StringType) [x] = op "number->string" [x]
schOp (Cast Bits64Type StringType) [x] = op "number->string" [x]
schOp (Cast DoubleType StringType) [x] = op "number->string" [x]
schOp (Cast CharType StringType) [x] = op "string" [x]

schOp (Cast IntType IntegerType) [x] = x
schOp (Cast Bits8Type IntegerType) [x] = x
schOp (Cast Bits16Type IntegerType) [x] = x
schOp (Cast Bits32Type IntegerType) [x] = x
schOp (Cast Bits64Type IntegerType) [x] = x
schOp (Cast DoubleType IntegerType) [x] = op "exact-floor" [x]
schOp (Cast CharType IntegerType) [x] = op "char->integer" [x]
schOp (Cast StringType IntegerType) [x] = op "cast-string-int" [x]

schOp (Cast IntegerType IntType) [x] = x
schOp (Cast Bits8Type IntType) [x] = x
schOp (Cast Bits16Type IntType) [x] = x
schOp (Cast Bits32Type IntType) [x] = x
schOp (Cast Bits64Type IntType) [x] = x
schOp (Cast DoubleType IntType) [x] = op "exact-floor" [x]
schOp (Cast StringType IntType) [x] = op "cast-string-int" [x]
schOp (Cast CharType IntType) [x] = op "char->integer" [x]

schOp (Cast IntType Bits8Type) [x] = op "integer->bits8" [x]
schOp (Cast IntType Bits16Type) [x] = op "integer->bits16" [x]
schOp (Cast IntType Bits32Type) [x] = op "integer->bits32" [x]
schOp (Cast IntType Bits64Type) [x] = op "integer->bits64" [x]

schOp (Cast IntegerType Bits8Type) [x] = op "integer->bits8" [x]
schOp (Cast IntegerType Bits16Type) [x] = op "integer->bits16" [x]
schOp (Cast IntegerType Bits32Type) [x] = op "integer->bits32" [x]
schOp (Cast IntegerType Bits64Type) [x] = op "integer->bits64" [x]

schOp (Cast Bits8Type Bits16Type) [x] = x
schOp (Cast Bits8Type Bits32Type) [x] = x
schOp (Cast Bits8Type Bits64Type) [x] = x

schOp (Cast Bits16Type Bits8Type) [x] = op "bits16->bits8" [x]
schOp (Cast Bits16Type Bits32Type) [x] = x
schOp (Cast Bits16Type Bits64Type) [x] = x

schOp (Cast Bits32Type Bits8Type) [x] = op "bits32->bits8" [x]
schOp (Cast Bits32Type Bits16Type) [x] = op "bits32->bits16" [x]
schOp (Cast Bits32Type Bits64Type) [x] = x

schOp (Cast Bits64Type Bits8Type) [x] = op "bits64->bits8" [x]
schOp (Cast Bits64Type Bits16Type) [x] = op "bits64->bits16" [x]
schOp (Cast Bits64Type Bits32Type) [x] = op "bits64->bits32" [x]


schOp (Cast IntegerType DoubleType) [x] = op "exact->inexact" [x]
schOp (Cast IntType DoubleType) [x] = op "exact->inexact" [x]
schOp (Cast StringType DoubleType) [x] = op "cast-string-double" [x]

schOp (Cast IntType CharType) [x] = op "cast-int-char" [x]

schOp (Cast from to) [x] = "(blodwen-error-quit \"Invalid cast " ++ show from ++ "->" ++ show to ++ "\")"

schOp BelieveMe [_,_,x] = x
schOp Crash [_,msg] = "(blodwen-error-quit (string-append \"ERROR: \" " ++ msg ++ "))"

||| Extended primitives for the scheme backend, outside the standard set of primFn
public export
data ExtPrim = NewIORef | ReadIORef | WriteIORef
             | NewArray | ArrayGet | ArraySet
             | GetField | SetField
             | VoidElim
             | SysOS | SysCodegen
             | OnCollect
             | OnCollectAny
             | MakeFuture
             | Unknown Name

export
Show ExtPrim where
  show NewIORef = "NewIORef"
  show ReadIORef = "ReadIORef"
  show WriteIORef = "WriteIORef"
  show NewArray = "NewArray"
  show ArrayGet = "ArrayGet"
  show ArraySet = "ArraySet"
  show GetField = "GetField"
  show SetField = "SetField"
  show VoidElim = "VoidElim"
  show SysOS = "SysOS"
  show SysCodegen = "SysCodegen"
  show OnCollect = "OnCollect"
  show OnCollectAny = "OnCollectAny"
  show MakeFuture = "MakeFuture"
  show (Unknown n) = "Unknown " ++ show n

||| Match on a user given name to get the scheme primitive
toPrim : Name -> ExtPrim
toPrim pn@(NS _ n)
    = cond [(n == UN "prim__newIORef", NewIORef),
            (n == UN "prim__readIORef", ReadIORef),
            (n == UN "prim__writeIORef", WriteIORef),
            (n == UN "prim__newArray", NewArray),
            (n == UN "prim__arrayGet", ArrayGet),
            (n == UN "prim__arraySet", ArraySet),
            (n == UN "prim__getField", GetField),
            (n == UN "prim__setField", SetField),
            (n == UN "void", VoidElim), -- DEPRECATED. TODO: remove when bootstrap has been updated
            (n == UN "prim__void", VoidElim),
            (n == UN "prim__os", SysOS),
            (n == UN "prim__codegen", SysCodegen),
            (n == UN "prim__onCollect", OnCollect),
            (n == UN "prim__onCollectAny", OnCollectAny),
            (n == UN "prim__makeFuture", MakeFuture)
            ]
           (Unknown pn)
toPrim pn = Unknown pn

export
mkWorld : String -> String
mkWorld res = res -- MkIORes is a newtype now! schConstructor 0 [res, "#f"] -- MkIORes

schConstant : (String -> String) -> Constant -> String
schConstant _ (I x) = show x
schConstant _ (BI x) = show x
schConstant _ (B8 x) = show x
schConstant _ (B16 x) = show x
schConstant _ (B32 x) = show x
schConstant _ (B64 x) = show x
schConstant schString (Str x) = schString x
schConstant _ (Ch x)
   = if (the Int (cast x) >= 32 && the Int (cast x) < 127)
        then "#\\" ++ cast x
        else "(integer->char " ++ show (the Int (cast x)) ++ ")"
schConstant _ (Db x) = show x
schConstant _ WorldVal = "#f"
schConstant _ IntType = "#t"
schConstant _ IntegerType = "#t"
schConstant _ Bits8Type = "#t"
schConstant _ Bits16Type = "#t"
schConstant _ Bits32Type = "#t"
schConstant _ Bits64Type = "#t"
schConstant _ StringType = "#t"
schConstant _ CharType = "#t"
schConstant _ DoubleType = "#t"
schConstant _ WorldType = "#t"

schCaseDef : Maybe String -> String
schCaseDef Nothing = ""
schCaseDef (Just tm) = "(else " ++ tm ++ ")"

export
schArglist : List Name -> String
schArglist [] = ""
schArglist [x] = schName x
schArglist (x :: xs) = schName x ++ " " ++ schArglist xs

mutual
  used : Name -> NamedCExp -> Bool
  used n (NmLocal fc n') = n == n'
  used n (NmRef _ _) = False
  used n (NmLam _ _ sc) = used n sc
  used n (NmLet _ _ v sc) = used n v || used n sc
  used n (NmApp _ f args) = used n f || anyTrue (map (used n) args)
  used n (NmCon _ _ _ args) = anyTrue (map (used n) args)
  used n (NmOp _ _ args) = anyTrue (toList (map (used n) args))
  used n (NmExtPrim _ _ args) = anyTrue (map (used n) args)
  used n (NmForce _ _ t) = used n t
  used n (NmDelay _ _ t) = used n t
  used n (NmConCase _ sc alts def)
      = used n sc || anyTrue (map (usedCon n) alts)
            || maybe False (used n) def
  used n (NmConstCase _ sc alts def)
      = used n sc || anyTrue (map (usedConst n) alts)
            || maybe False (used n) def
  used n _ = False

  usedCon : Name -> NamedConAlt -> Bool
  usedCon n (MkNConAlt _ _ _ sc) = used n sc

  usedConst : Name -> NamedConstAlt -> Bool
  usedConst n (MkNConstAlt _ sc) = used n sc

parameters (schExtPrim : Int -> ExtPrim -> List NamedCExp -> Core String,
            schString : String -> String)
  showTag : Name -> Maybe Int -> String
  showTag n (Just i) = show i
  showTag n Nothing = schString (show n)

  mutual
    schConAlt : Int -> String -> NamedConAlt -> Core String
    schConAlt i target (MkNConAlt n tag args sc)
        = pure $ "((" ++ showTag n tag ++ ") "
                      ++ bindArgs 1 args !(schExp i sc) ++ ")"
      where
        bindArgs : Int -> (ns : List Name) -> String -> String
        bindArgs i [] body = body
        bindArgs i (n :: ns) body
            = if used n sc
                 then "(let ((" ++ schName n ++ " " ++ "(vector-ref " ++ target ++ " " ++ show i ++ "))) "
                    ++ bindArgs (i + 1) ns body ++ ")"
                 else bindArgs (i + 1) ns body

    schConUncheckedAlt : Int -> String -> NamedConAlt -> Core String
    schConUncheckedAlt i target (MkNConAlt n tag args sc)
        = pure $ bindArgs 1 args !(schExp i sc)
      where
        bindArgs : Int -> (ns : List Name) -> String -> String
        bindArgs i [] body = body
        bindArgs i (n :: ns) body
            = if used n sc
                 then "(let ((" ++ schName n ++ " " ++ "(vector-ref " ++ target ++ " " ++ show i ++ "))) "
                    ++ bindArgs (i + 1) ns body ++ ")"
                 else bindArgs (i + 1) ns body

    schConstAlt : Int -> String -> NamedConstAlt -> Core String
    schConstAlt i target (MkNConstAlt c exp)
        = pure $ "((equal? " ++ target ++ " " ++ schConstant schString c ++ ") " ++ !(schExp i exp) ++ ")"

    -- oops, no traverse for Vect in Core
    schArgs : Int -> Vect n NamedCExp -> Core (Vect n String)
    schArgs i [] = pure []
    schArgs i (arg :: args) = pure $ !(schExp i arg) :: !(schArgs i args)

    export
    schExp : Int -> NamedCExp -> Core String
    schExp i (NmLocal fc n) = pure $ schName n
    schExp i (NmRef fc n) = pure $ schName n
    schExp i (NmLam fc x sc)
       = do sc' <- schExp i  sc
            pure $ "(lambda (" ++ schName x ++ ") " ++ sc' ++ ")"
    schExp i (NmLet fc x val sc)
       = do val' <- schExp i val
            sc' <- schExp i sc
            pure $ "(let ((" ++ schName x ++ " " ++ val' ++ ")) " ++ sc' ++ ")"
    schExp i (NmApp fc x [])
        = pure $ "(" ++ !(schExp i x) ++ ")"
    schExp i (NmApp fc x args)
        = pure $ "(" ++ !(schExp i x) ++ " " ++ showSep " " !(traverse (schExp i) args) ++ ")"
    schExp i (NmCon fc x tag args)
        = pure $ schConstructor schString x tag !(traverse (schExp i) args)
    schExp i (NmOp fc op args)
        = pure $ schOp op !(schArgs i args)
    schExp i (NmExtPrim fc p args)
        = schExtPrim i (toPrim p) args
    schExp i (NmForce fc lr t) = pure $ "(" ++ !(schExp i t) ++ ")"
    schExp i (NmDelay fc lr t) = pure $ "(lambda () " ++ !(schExp i t) ++ ")"
    schExp i (NmConCase fc sc [] def)
        = do tcode <- schExp (i+1) sc
             defc <- maybe (pure "'erased") (schExp i) def
             let n = "sc" ++ show i
             pure $ "(let ((" ++ n ++ " " ++ tcode ++ ")) "
                     ++ defc ++ ")"
    schExp i (NmConCase fc sc [alt] Nothing)
        = do tcode <- schExp (i+1) sc
             let n = "sc" ++ show i
             pure $ "(let ((" ++ n ++ " " ++ tcode ++ ")) " ++
                    !(schConUncheckedAlt (i+1) n alt) ++ ")"
    schExp i (NmConCase fc sc alts Nothing)
        = do tcode <- schExp (i+1) sc
             let n = "sc" ++ show i
             pure $ "(let ((" ++ n ++ " " ++ tcode ++ ")) (case (vector-ref " ++ n ++ " 0) "
                     ++ !(showAlts n alts) ++
                     "))"
      where
        showAlts : String -> List NamedConAlt -> Core String
        showAlts n [] = pure ""
        showAlts n [alt]
           = pure $ "(else " ++ !(schConUncheckedAlt (i + 1) n alt) ++ ")"
        showAlts n (alt :: alts)
           = pure $ !(schConAlt (i + 1) n alt) ++ " " ++
                    !(showAlts n alts)
    schExp i (NmConCase fc sc alts def)
        = do tcode <- schExp (i+1) sc
             defc <- maybe (pure Nothing) (\v => pure (Just !(schExp i v))) def
             let n = "sc" ++ show i
             pure $ "(let ((" ++ n ++ " " ++ tcode ++ ")) (case (vector-ref " ++ n ++ " 0) "
                     ++ showSep " " !(traverse (schConAlt (i+1) n) alts)
                     ++ schCaseDef defc ++ "))"
    schExp i (NmConstCase fc sc alts Nothing)
        = do tcode <- schExp (i+1) sc
             let n = "sc" ++ show i
             pure $ "(let ((" ++ n ++ " " ++ tcode ++ ")) (cond "
                      ++ !(showConstAlts n alts)
                      ++ "))"
      where
        showConstAlts : String -> List NamedConstAlt -> Core String
        showConstAlts n [] = pure ""
        showConstAlts n [MkNConstAlt c exp]
           = pure $ "(else " ++ !(schExp (i + 1) exp) ++ ")"
        showConstAlts n (alt :: alts)
           = pure $ !(schConstAlt (i + 1) n alt) ++ " " ++
                    !(showConstAlts n alts)
    schExp i (NmConstCase fc sc alts def)
        = do defc <- maybe (pure Nothing) (\v => pure (Just !(schExp i v))) def
             tcode <- schExp (i+1) sc
             let n = "sc" ++ show i
             pure $ "(let ((" ++ n ++ " " ++ tcode ++ ")) (cond "
                      ++ showSep " " !(traverse (schConstAlt (i+1) n) alts)
                      ++ schCaseDef defc ++ "))"
    schExp i (NmPrimVal fc c) = pure $ schConstant schString c
    schExp i (NmErased fc) = pure "'erased"
    schExp i (NmCrash fc msg) = pure $ "(blodwen-error-quit " ++ show msg ++ ")"

  -- Need to convert the argument (a list of scheme arguments that may
  -- have been constructed at run time) to a scheme list to be passed to apply
  readArgs : Int -> NamedCExp -> Core String
  readArgs i tm = pure $ "(blodwen-read-args " ++ !(schExp i tm) ++ ")"

  fileOp : String -> String
  fileOp op = "(blodwen-file-op (lambda () " ++ op ++ "))"

  -- External primitives which are common to the scheme codegens (they can be
  -- overridden)
  export
  schExtCommon : Int -> ExtPrim -> List NamedCExp -> Core String
  schExtCommon i NewIORef [_, val, world]
      = pure $ mkWorld $ "(box " ++ !(schExp i val) ++ ")"
  schExtCommon i ReadIORef [_, ref, world]
      = pure $ mkWorld $ "(unbox " ++ !(schExp i ref) ++ ")"
  schExtCommon i WriteIORef [_, ref, val, world]
      = pure $ mkWorld $ "(set-box! "
                           ++ !(schExp i ref) ++ " "
                           ++ !(schExp i val) ++ ")"
  schExtCommon i NewArray [_, size, val, world]
      = pure $ mkWorld $ "(make-vector " ++ !(schExp i size) ++ " "
                                         ++ !(schExp i val) ++ ")"
  schExtCommon i ArrayGet [_, arr, pos, world]
      = pure $ mkWorld $ "(vector-ref " ++ !(schExp i arr) ++ " "
                                        ++ !(schExp i pos) ++ ")"
  schExtCommon i ArraySet [_, arr, pos, val, world]
      = pure $ mkWorld $ "(vector-set! " ++ !(schExp i arr) ++ " "
                                         ++ !(schExp i pos) ++ " "
                                         ++ !(schExp i val) ++ ")"
  schExtCommon i VoidElim [_, _]
      = pure "(display \"Error: Executed 'void'\")"
  schExtCommon i SysOS []
      = pure $ "(blodwen-os)"
  schExtCommon i (Unknown n) args
      = throw (InternalError ("Can't compile unknown external primitive " ++ show n))
  schExtCommon i prim args
      = throw (InternalError ("Badly formed external primitive " ++ show prim
                                ++ " " ++ show args))

  schDef : {auto c : Ref Ctxt Defs} ->
           Name -> NamedDef -> Core String
  schDef n (MkNmFun args exp)
     = pure $ "(define " ++ schName !(getFullName n) ++ " (lambda (" ++ schArglist args ++ ") "
                      ++ !(schExp 0 exp) ++ "))\n"
  schDef n (MkNmError exp)
     = pure $ "(define (" ++ schName !(getFullName n) ++ " . any-args) " ++ !(schExp 0 exp) ++ ")\n"
  schDef n (MkNmForeign _ _ _) = pure "" -- compiled by specific back end
  schDef n (MkNmCon t a _) = pure "" -- Nothing to compile here

-- Convert the name to scheme code
-- (There may be no code generated, for example if it's a constructor)
export
getScheme : {auto c : Ref Ctxt Defs} ->
            (schExtPrim : Int -> ExtPrim -> List NamedCExp -> Core String) ->
            (schString : String -> String) ->
            (Name, FC, NamedDef) -> Core String
getScheme schExtPrim schString (n, fc, d)
    = schDef schExtPrim schString n d

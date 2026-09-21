||| Code common to all the scheme backend
|||
||| In most cases the inital `Nat` argument
||| is the number of cases a given expression is under.
||| it is used to generate new unique names for the scrutinee of a case block
module Compiler.Scheme.Common

import Compiler.Common
import Compiler.CompileExpr

import Core.Context

import Libraries.Data.String.Builder
import Data.SnocList

import Data.SortedSet
import Data.Vect

%default covering

export
firstExists : List String -> IO (Maybe String)
firstExists [] = pure Nothing
firstExists (x :: xs) = if !(exists x) then pure (Just x) else firstExists xs

schString : String -> Builder
schString s = concatMap okchar (unpack s)
  where
    okchar : Char -> Builder
    okchar c = if isAlphaNum c || c =='_'
                  then char c
                  else "C-" ++ showB (ord c)

export
schUserName : UserName -> Builder
schUserName (Basic n) = "u--" ++ schString n
schUserName (Field n) = "rf--" ++ schString n
schUserName Underscore = "u--_"

export
schName : Name -> Builder
schName (NS ns (UN (Basic n))) = schString (showNSWithSep "-" ns) ++ "-" ++ schString n
schName (UN n) = schUserName n
schName (NS ns n) = schString (showNSWithSep "-" ns) ++ "-" ++ schName n
schName (MN n i) = schString n ++ "-" ++ showB i
schName (PV n d) = "pat--" ++ schName n
schName (DN _ n) = schName n
schName (Nested (i, x) n) = "n--" ++ showB i ++ "-" ++ showB x ++ "-" ++ schName n
schName (CaseBlock x y) = "case--" ++ schString x ++ "-" ++ showB y
schName (WithBlock x y) = "with--" ++ schString x ++ "-" ++ showB y
schName (Resolved i) = "fn--" ++ showB i

export
schConstructor : (String -> Builder) -> Name -> Maybe Int -> List Builder -> Builder
schConstructor _ _ (Just t) args
    = "(vector " ++ showB t ++ " " ++ sepBy " " args ++ ")"
schConstructor schString n Nothing args
    = "(vector " ++ schString (show n) ++ " " ++ Builder.sepBy " " args ++ ")"

export
schRecordCon : (String -> Builder) -> Name -> List Builder -> Builder
schRecordCon _ _ args = "(vector " ++ sepBy " " args ++ ")"

||| Generate scheme for a plain function.
op : String -> List Builder -> Builder
op o args = "(" ++ singleton o ++ " " ++ sepBy " " args ++ ")"

||| Generate scheme for a boolean operation.
boolop : String -> List Builder -> Builder
boolop o args = "(or (and " ++ op o args ++ " 1) 0)"

add : Maybe IntKind -> Builder -> Builder -> Builder
add (Just $ Signed $ P n)   x y = op "bs+" [x, y, showB (n-1)]
add (Just $ Unsigned n)     x y = op "bu+" [x, y, showB n]
add _                       x y = op "+" [x, y]

sub : Maybe IntKind -> Builder -> Builder -> Builder
sub (Just $ Signed $ P n)   x y = op "bs-" [x, y, showB (n-1)]
sub (Just $ Unsigned n)     x y = op "bu-" [x, y, showB n]
sub _                       x y = op "-" [x, y]

mul : Maybe IntKind -> Builder -> Builder -> Builder
mul (Just $ Signed $ P n)   x y = op "bs*" [x, y, showB (n-1)]
mul (Just $ Unsigned n)     x y = op "bu*" [x, y, showB n]
mul _                       x y = op "*" [x, y]

div : Maybe IntKind -> Builder -> Builder -> Builder
div (Just $ Signed Unlimited) x y = op "blodwen-euclidDiv" [x, y]
div (Just $ Signed $ P n)     x y = op "bs/" [x, y, showB (n-1)]
div (Just $ Unsigned n)       x y = op "bu/" [x, y, showB n]
div _                         x y = op "/" [x, y]

shl : Maybe IntKind -> Builder -> Builder -> Builder
shl (Just $ Signed $ P n) x y = op "blodwen-bits-shl-signed"
                                   [x, y, showB (n-1)]
shl (Just $ Unsigned n)   x y = op "blodwen-bits-shl" [x, y, showB n]
shl _                     x y = op "blodwen-shl" [x, y]


constPrimitives : ConstantPrimitives' Builder
constPrimitives = MkConstantPrimitives {
    charToInt    = \k     => pure . charTo k
  , intToChar    = \_,x   => pure $ op "cast-int-char" [x]
  , stringToInt  = \k     => pure . strTo k
  , intToString  = \_,x   => pure $ op "number->string" [x]
  , doubleToInt  = \k     => pure . dblTo k
  , intToDouble  = \_,x   => pure $ op "exact->inexact" [x]
  , intToInt     = \k1,k2 => pure . intTo k1 k2
  }
  where charTo : IntKind -> Builder -> Builder
        charTo (Signed Unlimited) x = op "char->integer" [x]
        charTo (Signed $ P n)     x = op "cast-char-boundedInt" [x, showB (n-1)]
        charTo (Unsigned n)       x = op "cast-char-boundedUInt" [x, showB n]

        strTo : IntKind -> Builder -> Builder
        strTo (Signed Unlimited) x = op "cast-string-int" [x]
        strTo (Signed $ P n)     x = op "cast-string-boundedInt" [x, showB (n-1)]
        strTo (Unsigned n)       x = op "cast-string-boundedUInt" [x, showB n]

        dblTo : IntKind -> Builder -> Builder
        dblTo (Signed Unlimited) x = op "exact-truncate" [x]
        dblTo (Signed $ P n)     x = op "exact-truncate-boundedInt" [x, showB (n-1)]
        dblTo (Unsigned n)       x = op "exact-truncate-boundedUInt" [x, showB n]

        intTo : IntKind -> IntKind -> Builder -> Builder
        intTo _ (Signed Unlimited) x = x
        intTo (Signed m) (Signed $ P n) x =
          if P n >= m then x else op "blodwen-toSignedInt" [x, showB (n-1)]

        -- Only if the precision of the target is greater
        -- than the one of the source, there is no need to cast.
        intTo (Unsigned m) (Signed $ P n) x =
          if n > m then x else op "blodwen-toSignedInt" [x, showB (n-1)]

        intTo (Signed _) (Unsigned n) x = op "blodwen-toUnsignedInt" [x, showB n]

        intTo (Unsigned m) (Unsigned n) x =
          if n >= m then x else op "blodwen-toUnsignedInt" [x, showB n]

||| Generate scheme for a primitive function.
schOp : {0 arity : Nat} -> PrimFn arity -> Vect arity Builder -> Core Builder
schOp (Add ty) [x, y] = pure $ add (intKind ty) x y
schOp (Sub ty) [x, y] = pure $ sub (intKind ty) x y
schOp (Mul ty) [x, y] = pure $ mul (intKind ty) x y
schOp (Div ty) [x, y] = pure $ div (intKind ty) x y
schOp (Mod ty) [x, y] = pure $ op "blodwen-euclidMod" [x, y]
schOp (Neg ty) [x] = pure $ op "-" [x]
schOp (ShiftL ty) [x, y] = pure $ shl (intKind ty) x y
schOp (ShiftR ty) [x, y] = pure $ op "blodwen-shr" [x, y]
schOp (BAnd ty) [x, y] = pure $ op "blodwen-and" [x, y]
schOp (BOr ty) [x, y] = pure $ op "blodwen-or" [x, y]
schOp (BXOr ty) [x, y] = pure $ op "blodwen-xor" [x, y]
schOp (LT CharType) [x, y] = pure $ boolop "char<?" [x, y]
schOp (LTE CharType) [x, y] = pure $ boolop "char<=?" [x, y]
schOp (EQ CharType) [x, y] = pure $ boolop "char=?" [x, y]
schOp (GTE CharType) [x, y] = pure $ boolop "char>=?" [x, y]
schOp (GT CharType) [x, y] = pure $ boolop "char>?" [x, y]
schOp (LT StringType) [x, y] = pure $ boolop "string<?" [x, y]
schOp (LTE StringType) [x, y] = pure $ boolop "string<=?" [x, y]
schOp (EQ StringType) [x, y] = pure $ boolop "string=?" [x, y]
schOp (GTE StringType) [x, y] = pure $ boolop "string>=?" [x, y]
schOp (GT StringType) [x, y] = pure $ boolop "string>?" [x, y]
schOp (LT ty) [x, y] = pure $ boolop "<" [x, y]
schOp (LTE ty) [x, y] = pure $ boolop "<=" [x, y]
schOp (EQ ty) [x, y] = pure $ boolop "=" [x, y]
schOp (GTE ty) [x, y] = pure $ boolop ">=" [x, y]
schOp (GT ty) [x, y] = pure $ boolop ">" [x, y]
schOp StrLength [x] = pure $ op "string-length" [x]
schOp StrHead [x] = pure $ op "string-ref" [x, "0"]
schOp StrTail [x] = pure $ op "substring" [x, "1", op "string-length" [x]]
schOp StrIndex [x, i] = pure $ op "string-ref" [x, i]
schOp StrCons [x, y] = pure $ op "string-cons" [x, y]
schOp StrAppend [x, y] = pure $ op "string-append" [x, y]
schOp StrReverse [x] = pure $ op "string-reverse" [x]
schOp StrSubstr [x, y, z] = pure $ op "string-substr" [x, y, z]

-- `e` is Euler's number, which approximates to: 2.718281828459045
schOp DoubleExp [x] = pure $ op "flexp" [x] -- Base is `e`. Same as: `pow(e, x)`
schOp DoubleLog [x] = pure $ op "fllog" [x] -- Base is `e`.
schOp DoublePow [x, y] = pure $ op "flexpt" [x, y]
schOp DoubleSin [x] = pure $ op "flsin" [x]
schOp DoubleCos [x] = pure $ op "flcos" [x]
schOp DoubleTan [x] = pure $ op "fltan" [x]
schOp DoubleASin [x] = pure $ op "flasin" [x]
schOp DoubleACos [x] = pure $ op "flacos" [x]
schOp DoubleATan [x] = pure $ op "flatan" [x]
schOp DoubleSqrt [x] = pure $ op "flsqrt" [x]
schOp DoubleFloor [x] = pure $ op "flfloor" [x]
schOp DoubleCeiling [x] = pure $ op "flceiling" [x]

schOp (Cast DoubleType StringType)  [x] = pure $ op "number->string" [x]
schOp (Cast CharType StringType)    [x] = pure $ op "string" [x]
schOp (Cast StringType DoubleType)  [x] = pure $ op "cast-string-double" [x]

schOp (Cast from to)                [x] = castInt constPrimitives from to x

schOp BelieveMe [_,_,x] = pure x
schOp Crash [_,msg] = pure $ "(blodwen-error-quit (string-append \"ERROR: \" " ++ msg ++ "))"

||| Extended primitives for the scheme backend, outside the standard set of primFn
public export
data ExtPrim = NewIORef | ReadIORef | WriteIORef
             | NewArray | ArrayGet | ArraySet
             | GetField | SetField
             | SysOS | SysCodegen
             | OnCollect
             | OnCollectAny
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
  show SysOS = "SysOS"
  show SysCodegen = "SysCodegen"
  show OnCollect = "OnCollect"
  show OnCollectAny = "OnCollectAny"
  show (Unknown n) = "Unknown " ++ show n

||| Match on a user given name to get the scheme primitive
toPrim : Name -> ExtPrim
toPrim pn@(NS _ n)
    = cond [(n == UN (Basic "prim__newIORef"), NewIORef),
            (n == UN (Basic "prim__readIORef"), ReadIORef),
            (n == UN (Basic "prim__writeIORef"), WriteIORef),
            (n == UN (Basic "prim__newArray"), NewArray),
            (n == UN (Basic "prim__arrayGet"), ArrayGet),
            (n == UN (Basic "prim__arraySet"), ArraySet),
            (n == UN (Basic "prim__getField"), GetField),
            (n == UN (Basic "prim__setField"), SetField),
            (n == UN (Basic "prim__os"), SysOS),
            (n == UN (Basic "prim__codegen"), SysCodegen),
            (n == UN (Basic "prim__onCollect"), OnCollect),
            (n == UN (Basic "prim__onCollectAny"), OnCollectAny)
            ]
           (Unknown pn)
toPrim pn = Unknown pn

export
mkWorld : Builder -> Builder
mkWorld res = res -- MkIORes is a newtype now! schConstructor 0 [res, "#f"] -- MkIORes

schPrimType : PrimType -> Builder
schPrimType _ = "#t"

schConstant : (String -> Builder) -> Constant -> Builder
schConstant _ (I x) = showB x
schConstant _ (I8 x) = showB x
schConstant _ (I16 x) = showB x
schConstant _ (I32 x) = showB x
schConstant _ (I64 x) = showB x
schConstant _ (BI x) = showB x
schConstant _ (B8 x) = showB x
schConstant _ (B16 x) = showB x
schConstant _ (B32 x) = showB x
schConstant _ (B64 x) = showB x
schConstant schString (Str x) = schString x
schConstant _ (Ch x)
   = if (ord x >= 32 && ord x < 127)
        then "#\\" ++ char x
        else "(integer->char " ++ showB (ord x) ++ ")"
schConstant _ (Db x) = showB x
schConstant _ (PrT t) = schPrimType t
schConstant _ WorldVal = "#f"

schCaseDef : Maybe Builder -> Builder
schCaseDef Nothing = ""
schCaseDef (Just tm) = "(else " ++ tm ++ ")"

export
schArglist : List Name -> Builder
schArglist xs = sepBy " " $ map schName xs
-- schArglist [] = ""
-- schArglist [x] = schName x
-- schArglist (x :: xs) = schName x ++ " " ++ schArglist xs

mutual
  used : Name -> NamedCExp -> Bool
  used n (NmLocal fc n') = n == n'
  used n (NmRef {}) = False
  used n (NmLam _ _ sc) = used n sc
  used n (NmLet _ _ v sc) = used n v || used n sc
  used n (NmApp _ f args) = used n f || any (used n) args
  used n (NmCon _ _ _ _ args) = any (used n) args
  used n (NmOp _ _ args) = any (used n) (toList args)
  used n (NmExtPrim _ _ args) = any (used n) args
  used n (NmForce _ _ t) = used n t
  used n (NmDelay _ _ t) = used n t
  used n (NmConCase _ sc alts def)
      = used n sc || any (usedCon n) alts
            || maybe False (used n) def
  used n (NmConstCase _ sc alts def)
      = used n sc || any (usedConst n) alts
            || maybe False (used n) def
  used n _ = False

  usedCon : Name -> NamedConAlt -> Bool
  usedCon n (MkNConAlt _ _ _ _ sc) = used n sc

  usedConst : Name -> NamedConstAlt -> Bool
  usedConst n (MkNConstAlt _ sc) = used n sc

var : NamedCExp -> Bool
var (NmLocal {}) = True
var _ = False

getScrutineeTemp : Nat -> Builder
getScrutineeTemp i = fromString $ "sc" ++ show i

public export
record LazyExprProc where
  constructor MkLazyExprProc
  processDelay : Builder -> Builder
  processForce : Builder -> Builder

public export
defaultLaziness : LazyExprProc
defaultLaziness = MkLazyExprProc
  (\expr => "(lambda () " ++ expr ++ ")")
  (\expr => "(" ++ expr ++ ")")

public export
weakMemoLaziness : LazyExprProc
weakMemoLaziness = MkLazyExprProc
  (\expr => "(blodwen-delay-lazy (lambda () " ++ expr ++ "))")
  (\expr => "(blodwen-force-lazy " ++ expr ++ ")")

parameters (constants : SortedSet Name)
           (schExtPrim : Nat -> ExtPrim -> List NamedCExp -> Core Builder)
           (schString : String -> Builder)
           (schLazy : LazyExprProc)
  showTag : Name -> Maybe Int -> Builder
  showTag n (Just i) = showB i
  showTag n Nothing = schString (show n)

  mutual
    ||| Bind arguments of a data constructor represented by a vector
    ||| @ target the data constructor
    ||| @ sc the scope (ie the RHS of the alternative)
    ||| @ i the index to start at (1 for a regular data type, 0 for a record)
    ||| @ ns the names to bind in order
    ||| @ body the body of the alternative
    bindArgs : (target : Builder) -> (sc : NamedCExp) -> (i : Nat) -> (ns : List Name) -> (body : Builder) -> Builder
    bindArgs target sc i [] body = body
    bindArgs target sc i (n :: ns) body
        = if used n sc
                then "(let ((" ++ schName n ++ " " ++ "(vector-ref " ++ target ++ " " ++ showB i ++ "))) "
                ++ bindArgs target sc (i + 1) ns body ++ ")"
                else bindArgs target sc (i + 1) ns body

    schConAlt : Nat -> Builder -> NamedConAlt -> Core Builder
    schConAlt i target (MkNConAlt n ci tag args sc)
        = pure $ "((" ++ showTag n tag ++ ") "
                      ++ bindArgs target sc 1 args !(schExp i sc) ++ ")"

    schConUncheckedAlt : Nat -> Builder -> NamedConAlt -> Core Builder
    schConUncheckedAlt i target (MkNConAlt n ci tag args sc)
        = pure $ bindArgs target sc 1 args !(schExp i sc)

    schConstAlt : Nat -> Builder -> NamedConstAlt -> Core Builder
    schConstAlt i target (MkNConstAlt c exp)
        = pure $ "((equal? " ++ target ++ " " ++ schConstant schString c ++ ") " ++ !(schExp i exp) ++ ")"

    -- oops, no traverse for Vect in Core
    schArgs : Nat -> Vect n NamedCExp -> Core (Vect n Builder)
    schArgs i xs = traverseVect (schExp i) xs
    -- schArgs i [] = pure []
    -- schArgs i (arg :: args) = pure $ !(schExp i arg) :: !(schArgs i args)

    schCaseTree : Nat -> NamedCExp -> List NamedConAlt -> Maybe NamedCExp ->
                  Core Builder
    schCaseTree i sc [] def
        = do tcode <- schExp (i + 1) sc
             defc <- maybe (pure "'erased") (schExp i) def
             let n = getScrutineeTemp i
             if var sc
                then pure defc
                else pure $ "(let ((" ++ n ++ " " ++ tcode ++ ")) "
                             ++ defc ++ ")"
    schCaseTree i sc [alt] Nothing
        = do tcode <- schExp (i + 1) sc
             let n = getScrutineeTemp i
             if var sc
                then pure !(schConUncheckedAlt (i + 1) tcode alt)
                else pure $ "(let ((" ++ n ++ " " ++ tcode ++ ")) " ++
                        !(schConUncheckedAlt (i + 1) n alt) ++ ")"
    schCaseTree i sc alts Nothing
        = do tcode <- schExp (i + 1) sc
             let n = getScrutineeTemp i
             if var sc
                then pure $ "(case (vector-ref " ++ tcode ++ " 0) "
                       ++ !(showAlts tcode alts) ++
                       ")"
                else pure $ "(let ((" ++ n ++ " " ++ tcode ++ ")) (case (vector-ref " ++ n ++ " 0) "
                       ++ !(showAlts n alts) ++
                       "))"
      where
        showAlts : Builder -> List NamedConAlt -> Core Builder
        showAlts n [] = pure ""
        showAlts n [alt]
           = pure $ "(else " ++ !(schConUncheckedAlt (i + 1) n alt) ++ ")"
        showAlts n (alt :: alts)
           = pure $ !(schConAlt (i + 1) n alt) ++ " " ++
                    !(showAlts n alts)
    schCaseTree i sc alts def
        = do tcode <- schExp (i + 1) sc
             defc <- maybe (pure Nothing) (\v => pure (Just !(schExp i v))) def
             let n = getScrutineeTemp i
             if var sc
                then pure $ "(case (vector-ref " ++ tcode ++ " 0) "
                               ++ sepBy " " !(traverse (schConAlt (i + 1) tcode) alts)
                               ++ schCaseDef defc ++ ")"
                else pure $ "(let ((" ++ n ++ " " ++ tcode ++ ")) (case (vector-ref " ++ n ++ " 0) "
                       ++ sepBy " " !(traverse (schConAlt (i + 1) n) alts)
                       ++ schCaseDef defc ++ "))"

    schRecordCase : Nat -> NamedCExp -> List NamedConAlt -> Maybe NamedCExp ->
                    Core Builder
    schRecordCase i sc [] _ = pure "#f" -- suggests empty case block!
    schRecordCase i sc [alt] _
        = do tcode <- schExp (i + 1) sc
             let n = getScrutineeTemp i
             if var sc
                then getAltCode tcode alt
                else do alt' <- getAltCode n alt
                        pure $ "(let ((" ++ n ++ " " ++ tcode ++ ")) " ++
                                     alt' ++ ")"
      where
        getAltCode : Builder -> NamedConAlt -> Core Builder
        getAltCode n (MkNConAlt _ _ _ args sc)
            = pure $ bindArgs n sc 0 args !(schExp i sc)
    schRecordCase _ _ _ _ = throw $ InternalError "Case of a record has multiple alternatives"

    schListCase : Nat -> NamedCExp -> List NamedConAlt -> Maybe NamedCExp ->
                  Core Builder
    schListCase i sc alts def
        = do tcode <- schExp (i + 1) sc
             let n = getScrutineeTemp i
             defc <- maybe (pure Nothing)
                           (\v => pure (Just !(schExp (i + 1) v))) def
             nil <- getNilCode alts
             if var sc
                then do cons <- getConsCode tcode alts
                        pure $ buildCase tcode nil cons defc
                else do cons <- getConsCode n alts
                        pure $ "(let ((" ++ n ++ " " ++ tcode ++ ")) " ++
                            buildCase n nil cons defc ++ ")"
      where
        buildCase : Builder ->
                    Maybe Builder -> Maybe Builder -> Maybe Builder ->
                    Builder
        buildCase n (Just nil) (Just cons) _
            = "(if (null? " ++ n ++ ") " ++ nil ++ " " ++ cons ++ ")"
        buildCase n (Just nil) Nothing Nothing = nil
        buildCase n Nothing (Just cons) Nothing = cons
        buildCase n (Just nil) Nothing (Just def)
            = "(if (null? " ++ n ++ ") " ++ nil ++ " " ++ def ++ ")"
        buildCase n Nothing (Just cons) (Just def)
            = "(if (null? " ++ n ++ ") " ++ def ++ " " ++ cons ++ ")"
        buildCase n Nothing Nothing (Just def) = def
        buildCase n Nothing Nothing Nothing = "#f"

        getNilCode : List NamedConAlt -> Core (Maybe Builder)
        getNilCode [] = pure Nothing
        getNilCode (MkNConAlt _ NIL _ _ sc :: _)
            = pure (Just !(schExp (i + 1) sc))
        getNilCode (_ :: xs) = getNilCode xs

        getConsCode : Builder -> List NamedConAlt -> Core (Maybe Builder)
        getConsCode n [] = pure Nothing
        getConsCode n (MkNConAlt _ CONS _ [x,xs] sc :: _)
            = do sc' <- schExp (i + 1) sc
                 pure $ Just $ bindArgs [(x, "car"), (xs, "cdr")] sc'
          where
            bindArgs : (ns : List (Name, Builder)) -> Builder -> Builder
            bindArgs [] body = body
            bindArgs ((x, get) :: ns) body
                = if used x sc
                     then "(let ((" ++ schName x ++ " " ++ "(" ++ get ++ " " ++ n ++ "))) "
                        ++ bindArgs ns body ++ ")"
                     else bindArgs ns body
        getConsCode x (_ :: xs) = getConsCode x xs

    schMaybeCase : Nat -> NamedCExp -> List NamedConAlt -> Maybe NamedCExp ->
                   Core Builder
    schMaybeCase i sc alts def
        = do tcode <- schExp (i + 1) sc
             let n = getScrutineeTemp i
             defc <- maybe (pure Nothing)
                           (\v => pure (Just !(schExp (i + 1) v))) def
             nothing <- getNothingCode alts
             if var sc
                then do just <- getJustCode tcode alts
                        pure $ buildCase tcode nothing just defc
                else do just <- getJustCode n alts
                        pure $ "(let ((" ++ n ++ " " ++ tcode ++ ")) " ++
                            buildCase n nothing just defc ++ ")"
      where
        buildCase : Builder ->
                    Maybe Builder -> Maybe Builder -> Maybe Builder ->
                    Builder
        buildCase n (Just nothing) (Just just) _
            = "(if (null? " ++ n ++ ") " ++ nothing ++ " " ++ just ++ ")"
        buildCase n (Just nothing) Nothing Nothing = nothing
        buildCase n Nothing (Just just) Nothing = just
        buildCase n (Just nothing) Nothing (Just def)
            = "(if (null? " ++ n ++ ") " ++ nothing ++ " " ++ def ++ ")"
        buildCase n Nothing (Just just) (Just def)
            = "(if (null? " ++ n ++ ") " ++ def ++ " " ++ just ++ ")"
        buildCase n Nothing Nothing (Just def) = def
        buildCase n Nothing Nothing Nothing = "#f"

        getNothingCode : List NamedConAlt -> Core (Maybe Builder)
        getNothingCode [] = pure Nothing
        getNothingCode (MkNConAlt _ NOTHING _ _ sc :: _)
            = pure (Just !(schExp (i + 1) sc))
        getNothingCode (_ :: xs) = getNothingCode xs

        getJustCode : Builder -> List NamedConAlt -> Core (Maybe Builder)
        getJustCode n [] = pure Nothing
        getJustCode n (MkNConAlt _ JUST _ [x] sc :: _)
            = do sc' <- schExp (i + 1) sc
                 pure $ Just $ bindArg x sc'
          where
            bindArg : Name -> Builder -> Builder
            bindArg x body
                = if used x sc
                     then "(let ((" ++ schName x ++ " " ++ "(unbox " ++ n ++ "))) "
                        ++ body ++ ")"
                     else body
        getJustCode x (_ :: xs) = getJustCode x xs

    export
    schExp : Nat -> NamedCExp -> Core Builder
    schExp i (NmLocal fc n) = pure $ schName n
    schExp i (NmRef fc n) = pure $ schName n
    schExp i (NmLam fc x sc)
       = do sc' <- schExp i sc
            pure $ "(lambda (" ++ schName x ++ ") " ++ sc' ++ ")"
    schExp i (NmLet fc x val sc)
       = do val' <- schExp i val
            sc' <- schExp i sc
            pure $ "(let ((" ++ schName x ++ " " ++ val' ++ ")) " ++ sc' ++ ")"
    schExp i (NmApp fc x@(NmRef exp n) []) =
      if contains n constants
        then schExp i x
        else pure $ "(" ++ !(schExp i x) ++ ")"

    schExp i (NmApp fc x args)
        = pure $ "(" ++ !(schExp i x) ++ " " ++ sepBy " " !(traverse (schExp i) args) ++ ")"
    schExp i (NmCon fc _ NIL tag []) = pure $ "'()"
    schExp i (NmCon fc _ NIL tag _) = throw (InternalError "Bad NIL")
    schExp i (NmCon fc _ CONS tag [x, xs])
        = do x' <- schExp i x
             xs' <- schExp i xs
             pure $ "(cons " ++ x' ++ " " ++ xs' ++ ")"
    schExp i (NmCon fc _ CONS tag _) = throw (InternalError "Bad CONS")
    schExp i (NmCon fc _ NOTHING tag []) = pure $ "'()"
    schExp i (NmCon fc _ NOTHING tag _) = throw (InternalError "Bad NOTHING")
    schExp i (NmCon fc _ JUST tag [x])
        = do x' <- schExp i x
             pure $ "(box " ++ x' ++ ")"
    schExp i (NmCon fc _ JUST tag _) = throw (InternalError "Bad JUST")
    schExp i (NmCon fc x RECORD tag args)
        = pure $ schRecordCon schString x !(traverse (schExp i) args)
    schExp i (NmCon fc x ci tag args)
        = pure $ schConstructor schString x tag !(traverse (schExp i) args)
    schExp i (NmOp fc op args)
        = schOp op !(schArgs i args)
    schExp i (NmExtPrim fc p args)
        = schExtPrim i (toPrim p) args
    schExp i (NmForce _ _ (NmApp fc x@(NmRef {}) []))
       = pure $ "(force " ++ !(schExp i x) ++ ")" -- Special version for memoized toplevel lazy definitions
    schExp i (NmForce fc lr t) = pure $ schLazy.processForce !(schExp i t)
    schExp i (NmDelay fc lr t) = pure $ schLazy.processDelay !(schExp i t)
    schExp i (NmConCase fc sc alts def)
        = cond [(recordCase alts, schRecordCase i sc alts def),
                (maybeCase alts, schMaybeCase i sc alts def),
                (listCase alts, schListCase i sc alts def)]
                -- probably more to come here...
                (schCaseTree i sc alts def)
      where
        listCase : List NamedConAlt -> Bool
        listCase (MkNConAlt _ NIL _ _ _ :: _) = True
        listCase (MkNConAlt _ CONS _ _ _ :: _) = True
        listCase _ = False

        maybeCase : List NamedConAlt -> Bool
        maybeCase (MkNConAlt _ NOTHING _ _ _ :: _) = True
        maybeCase (MkNConAlt _ JUST _ _ _ :: _) = True
        maybeCase _ = False

        recordCase : List NamedConAlt -> Bool
        recordCase (MkNConAlt _ RECORD _ _ _ :: _) = True
        recordCase _ = False

    schExp i (NmConstCase fc sc alts Nothing)
        = do tcode <- schExp (i + 1) sc
             let n = getScrutineeTemp i
             if var sc
                then pure $ "(cond "
                          ++ !(showConstAlts tcode alts)
                          ++ ")"
                else pure $ "(let ((" ++ n ++ " " ++ tcode ++ ")) (cond "
                          ++ !(showConstAlts n alts)
                          ++ "))"
      where
        showConstAlts : Builder -> List NamedConstAlt -> Core Builder
        showConstAlts n [] = pure ""
        showConstAlts n [MkNConstAlt c exp]
           = pure $ "(else " ++ !(schExp (i + 1) exp) ++ ")"
        showConstAlts n (alt :: alts)
           = pure $ !(schConstAlt (i + 1) n alt) ++ " " ++
                    !(showConstAlts n alts)
    schExp i (NmConstCase fc sc alts def)
        = do defc <- maybe (pure Nothing) (\v => pure (Just !(schExp i v))) def
             tcode <- schExp (i + 1) sc
             let n = getScrutineeTemp i
             if var sc
                then pure $ "(cond "
                          ++ sepBy " " !(traverse (schConstAlt (i + 1) tcode) alts)
                          ++ schCaseDef defc ++ ")"
                else pure $ "(let ((" ++ n ++ " " ++ tcode ++ ")) (cond "
                          ++ sepBy " " !(traverse (schConstAlt (i + 1) n) alts)
                          ++ schCaseDef defc ++ "))"
    schExp i (NmPrimVal fc c) = pure $ schConstant schString c
    schExp i (NmErased fc) = pure "'erased"
    schExp i (NmCrash fc msg) = pure $ "(blodwen-error-quit " ++ showB msg ++ ")"

  -- External primitives which are common to the scheme codegens (they can be
  -- overridden)
  export
  schExtCommon : Nat -> ExtPrim -> List NamedCExp -> Core Builder
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
  schExtCommon i SysOS []
      = pure $ "(blodwen-os)"
  schExtCommon i (Unknown n) args
      = throw (InternalError ("Can't compile unknown external primitive " ++ show n))
  schExtCommon i prim args
      = throw (InternalError ("Badly formed external primitive " ++ show prim
                                ++ " " ++ show args))

  schDef : {auto c : Ref Ctxt Defs} ->
           Name -> NamedDef -> Core Builder

  schDef n (MkNmFun [] (NmDelay _ _ exp))
    = pure $ "(define " ++ schName !(getFullName n) ++ "(delay "
                     ++ !(schExp 0 exp) ++ "))\n" -- Special version for memoized toplevel lazy definitions

  schDef n (MkNmFun [] exp)
     = if contains n constants
          then pure $ "(define " ++ schName !(getFullName n) ++ " " ++ !(schExp 0 exp) ++ ")\n"
          else pure $ "(define " ++ schName !(getFullName n) ++ " (lambda () " ++ !(schExp 0 exp) ++ "))\n"


  schDef n (MkNmFun args exp)
     = pure $ "(define " ++ schName !(getFullName n) ++ " (lambda (" ++ schArglist args ++ ") "
                      ++ !(schExp 0 exp) ++ "))\n"
  schDef n (MkNmError exp)
     = pure $ "(define (" ++ schName !(getFullName n) ++ " . any-args) " ++ !(schExp 0 exp) ++ ")\n"
  schDef n (MkNmForeign {}) = pure "" -- compiled by specific back end
  schDef n (MkNmCon t a _) = pure "" -- Nothing to compile here

-- Convert the name to scheme code
-- (There may be no code generated, for example if it's a constructor)
export
getScheme : {auto c : Ref Ctxt Defs} ->
            (constants  : SortedSet Name) ->
            (schExtPrim : Nat -> ExtPrim -> List NamedCExp -> Core Builder) ->
            (schString : String -> Builder) ->
            (schLazy : LazyExprProc) ->
            (Name, FC, NamedDef) -> Core Builder
getScheme constants schExtPrim schString schLazy (n, fc, d)
    = schDef constants schExtPrim schString schLazy n d

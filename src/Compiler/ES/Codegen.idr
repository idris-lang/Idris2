module Compiler.ES.Codegen

import Compiler.Common
import Core.CompileExpr
import Core.Context
import Core.Directory
import Core.Options
import Data.Strings
import Compiler.ES.Ast
import Compiler.ES.Doc
import Compiler.ES.ToAst
import Compiler.ES.TailRec
import Compiler.ES.State
import Libraries.Data.SortedMap
import Libraries.Utils.Hex
import Libraries.Data.String.Extra

import Data.Vect

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

breakDrop1 : Char -> String -> (String, String)
breakDrop1 c = mapSnd (drop 1) . break (== c)

stringList : List String -> String
stringList = concat . intersperse "," . map show

--------------------------------------------------------------------------------
--          JS Strings
--------------------------------------------------------------------------------

export
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

export
jsStringDoc : String -> Doc
jsStringDoc = Text . jsString

export
esName : String -> String
esName x = "_" ++ x

jsIdent : String -> String
jsIdent s = concatMap okchar (unpack s)
  where
    okchar : Char -> String
    okchar '_' = "_"
    okchar c = if isAlphaNum c
                  then cast c
                  else "x" ++ the (String) (asHex (cast {to=Int} c))

keywordSafe : String -> String
keywordSafe "var" = "var_"
keywordSafe s = s

--------------------------------------------------------------------------------
--          JS Name
--------------------------------------------------------------------------------

export
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

export
jsNameDoc : Name -> Doc
jsNameDoc = Text . jsName

export
commentName : Name -> String
commentName (NS ns n@(RF _)) = show ns ++ ".(" ++ commentName n ++ ")"
commentName (NS ns n) = show ns ++ "." ++ commentName n
commentName (UN x) = x
commentName (MN x y) = "{" ++ x ++ ":" ++ show y ++ "}"
commentName (PV n d) = "{P:" ++ commentName n ++ ":" ++ show d ++ "}"
commentName (DN _ n) = commentName n
commentName (RF n) = "." ++ n
commentName (Nested (outer, idx) inner)
      = show outer ++ ":" ++ show idx ++ ":" ++ commentName inner
commentName (CaseBlock outer i) = "case block in " ++ outer
commentName (WithBlock outer i) = "with block in " ++ outer
commentName (Resolved x) = "$resolved" ++ show x

export
mainExpr : Name
mainExpr = MN "__mainExpression" 0

--------------------------------------------------------------------------------
--          Pretty Printing
--------------------------------------------------------------------------------

export
var : Var -> Doc
var (VName x) = jsNameDoc x
var (VLoc x)  = Text $ "$" ++ asHex x
var (VRef x)  = Text $ "$R" ++ asHex x

export
minimal : Minimal -> Doc
minimal (MVar v)          = var v
minimal (MProjection n v) = minimal v <+> ".a" <+> shown n

export
tag2es : Either Int Name -> Doc
tag2es (Left x)  = shown x
tag2es (Right x) = jsStringDoc $ show x

export
constant : Doc -> Doc -> Doc
constant n d = "const" <++> n <+> softEq <+> d <+> ";"

export
applyList : (lparen : Doc) -> (rparen : Doc) -> (sep : Doc) -> List Doc -> Doc
applyList l r sep ds = l <+> (concat $ intersperse sep ds) <+> r

export
applyCon : (tag : Either Int Name) -> (args : List Doc) -> Doc
applyCon tag args =
  let argPairs =
        zipWith (\i,a => hcat ["a",shown i,softColon,a])
                [1..length args]
                args
   in applyList "{" "}" softComma (("h" <+> softColon <+> tag2es tag)::argPairs)

export
app : Doc -> List Doc -> Doc
app d args = d <+> applyList "(" ")" softComma args

callFun : String -> List Doc -> Doc
callFun = app . Text

callFun1 : String -> Doc -> Doc
callFun1 fun = callFun fun . pure

export
jsCrashExp : Doc -> Doc
jsCrashExp = callFun1 (esName "crashExp")

export
function : Doc -> (args : List Doc) -> (body : Doc) -> Doc
function n args body =
  "function" <++> app n args <+> SoftSpace <+> block body

--------------------------------------------------------------------------------
--          Primitives
--------------------------------------------------------------------------------

toBigInt : Doc -> Doc
toBigInt = callFun1 "BigInt"

fromBigInt : Doc -> Doc
fromBigInt = callFun1 "Number"

useBigInt' : Int -> Bool
useBigInt' = (> 32)

useBigInt : IntKind -> Bool
useBigInt (Signed $ P x)     = useBigInt' x
useBigInt (Signed Unlimited) = True
useBigInt (Unsigned x)       = useBigInt' x

jsBigIntOfString : Doc -> Doc
jsBigIntOfString = callFun1 (esName "bigIntOfString")

jsNumberOfString : Doc -> Doc
jsNumberOfString = callFun1 "parseFloat"

jsIntOfString : IntKind -> Doc -> Doc
jsIntOfString k = if useBigInt k then jsBigIntOfString else jsNumberOfString

binOp : String -> Doc -> Doc -> Doc
binOp o lhs rhs = hcat ["(", lhs, Text o, rhs, ")"]

adjInt : Int -> Doc -> Doc
adjInt bits = if useBigInt' bits then toBigInt else id

toInt : IntKind -> Doc -> Doc
toInt k = if useBigInt k then toBigInt else id

fromInt : IntKind -> Doc -> Doc
fromInt k = if useBigInt k then fromBigInt else id

jsIntOfChar : IntKind -> Doc -> Doc
jsIntOfChar k s = toInt k $ s <+> ".codePointAt(0)"

jsIntOfDouble : IntKind -> Doc -> Doc
jsIntOfDouble k = toInt k . callFun1 "Math.trunc"

jsAnyToString : Doc -> Doc
jsAnyToString s = "(''+" <+> s <+> ")"

-- Valid unicode code poing range is [0,1114111], therefore,
-- we calculate the remainder modulo 1114112 (= 17 * 2^16).
jsCharOfInt : IntKind -> Doc -> Doc
jsCharOfInt k = callFun1 (esName "truncToChar") . fromInt k

-- We can't determine `isBigInt` from the given number of bits, since
-- when casting from BigInt to Number we need to truncate the BigInt
-- first, otherwise we might lose precision
truncateSigned : (isBigInt : Bool) -> Int -> Doc -> Doc
truncateSigned isBigInt bits =
   let add = if isBigInt then "BigInt" else "Int"
    in callFun1 (esName "trunc" ++ add ++ show bits)

truncateUnsigned : (isBigInt : Bool) -> Int -> Doc -> Doc
truncateUnsigned isBigInt bits =
   let add = if isBigInt then "BigInt" else "Int"
    in callFun1 (esName "truncU" ++ add ++ show bits)

boundedOp : (suffix : String) -> Int -> String -> Doc -> Doc -> Doc
boundedOp s bits o x y = callFun (concat {t=List} ["_", o, show bits, s]) [x,y]

boundedIntOp : Int -> String -> Doc -> Doc -> Doc
boundedIntOp = boundedOp "s"

boundedUIntOp : Int -> String -> Doc -> Doc -> Doc
boundedUIntOp = boundedOp "u"

boolOp : String -> Doc -> Doc -> Doc
boolOp o lhs rhs = "(" <+> binOp o lhs rhs <+> "?1n:0n)"

export
jsConstant : Constant -> Core String
jsConstant (I i)    = pure $ show i ++ "n"
jsConstant (I8 i)   = pure $ show i
jsConstant (I16 i)  = pure $ show i
jsConstant (I32 i)  = pure $ show i
jsConstant (I64 i)  = pure $ show i ++ "n"
jsConstant (BI i)   = pure $ show i ++ "n"
jsConstant (Str s)  = pure $ jsString s
jsConstant (Ch c)   = pure . jsString $ singleton c
jsConstant (Db f)   = pure $ show f
jsConstant WorldVal = pure $ esName "idrisworld"
jsConstant (B8 i)   = pure $ show i
jsConstant (B16 i)  = pure $ show i
jsConstant (B32 i)  = pure $ show i
jsConstant (B64 i)  = pure $ show i ++ "n"
jsConstant ty       = error $ "Unsuported constant " ++ show ty

-- Creates the definition of a binary arithmetic operation.
-- Rounding / truncation behavior is determined from the
-- `IntKind`.
arithOp :  Maybe IntKind
        -> (sym : String)
        -> (op : String)
        -> (x : Doc)
        -> (y : Doc)
        -> Doc
arithOp (Just $ Signed $ P n) _   op = boundedIntOp n op
arithOp (Just $ Unsigned n)   _   op = boundedUIntOp n op
arithOp _                     sym _  = binOp sym

castInt : Constant -> Constant -> Doc -> Core Doc
castInt from to x =
  case ((from, intKind from), (to, intKind to)) of
    ((CharType,_),  (_,Just k)) => truncInt (useBigInt k) k $ jsIntOfChar k x
    ((StringType,_),(_,Just k)) => truncInt (useBigInt k) k (jsIntOfString k x)
    ((DoubleType,_),(_,Just k)) => truncInt (useBigInt k) k $ jsIntOfDouble k x
    ((_,Just k),(CharType,_))   => pure $ jsCharOfInt k x
    ((_,Just k),(StringType,_)) => pure $ jsAnyToString x
    ((_,Just k),(DoubleType,_)) => pure $ fromInt k x
    ((_,Just k1),(_,Just k2))   => intImpl k1 k2
    _ => errorConcat $ ["invalid cast: + ",show from," + ' -> ' + ",show to]
  where
    truncInt : (isBigInt : Bool) -> IntKind -> Doc -> Core Doc
    truncInt b (Signed Unlimited) = pure
    truncInt b (Signed $ P n)     = pure . truncateSigned b n
    truncInt b (Unsigned n)       = pure . truncateUnsigned b n

    shrink : IntKind -> IntKind -> Doc -> Doc
    shrink k1 k2 = case (useBigInt k1, useBigInt k2) of
                        (True, False) => fromBigInt
                        _             => id

    expand : IntKind -> IntKind -> Doc -> Doc
    expand k1 k2 = case (useBigInt k1, useBigInt k2) of
                        (False,True) => toBigInt
                        _            => id

    -- when going from BigInt to Number, we must make
    -- sure to first truncate the BigInt, otherwise we
    -- might get rounding issues
    intImpl : IntKind -> IntKind -> Core Doc
    intImpl k1 k2 =
      let expanded = expand k1 k2 x
          shrunk   = shrink k1 k2 <$> truncInt (useBigInt k1) k2 x
       in case (k1,k2) of
            (_, Signed Unlimited)    => pure $ expanded
            (Signed m, Signed n)     =>
              if n >= m then pure expanded else shrunk

            (Signed _, Unsigned n)   =>
              case (useBigInt k1, useBigInt k2) of
                   (False,True)  => truncInt True k2 (toBigInt x)
                   _             => shrunk

            (Unsigned m, Unsigned n) =>
              if n >= m then pure expanded else shrunk

            -- Only if the precision of the target is greater
            -- than the one of the source, there is no need to cast.
            (Unsigned m, Signed n)   =>
              if n > P m then pure expanded else shrunk

export
jsOp : {0 arity : Nat} ->
       PrimFn arity -> Vect arity Doc -> Core Doc
jsOp (Add ty) [x, y] = pure $ arithOp (intKind ty) "+" "add" x y
jsOp (Sub ty) [x, y] = pure $ arithOp (intKind ty) "-" "sub" x y
jsOp (Mul ty) [x, y] = pure $ arithOp (intKind ty) "*" "mul" x y
jsOp (Div ty) [x, y] = pure $ arithOp (intKind ty) "/" "div" x y
jsOp (Mod ty) [x, y] = pure $ binOp "%" x y
jsOp (Neg ty) [x] = pure $ "(-(" <+> x <+> "))"
jsOp (ShiftL Int32Type) [x, y] = pure $ binOp "<<" x y
jsOp (ShiftL ty) [x, y] = pure $ arithOp (intKind ty) "<<" "shl" x y
jsOp (ShiftR Int32Type) [x, y] = pure $ binOp ">>" x y
jsOp (ShiftR ty) [x, y] = pure $ arithOp (intKind ty) ">>" "shr" x y
jsOp (BAnd Bits32Type) [x, y] = pure $ boundedUIntOp 32 "and" x y
jsOp (BOr Bits32Type) [x, y]  = pure $ boundedUIntOp 32 "or" x y
jsOp (BXOr Bits32Type) [x, y] = pure $ boundedUIntOp 32 "xor" x y
jsOp (BAnd ty) [x, y] = pure $ binOp "&" x y
jsOp (BOr ty) [x, y] = pure $ binOp "|" x y
jsOp (BXOr ty) [x, y] = pure $ binOp "^" x y
jsOp (LT ty) [x, y] = pure $ boolOp "<" x y
jsOp (LTE ty) [x, y] = pure $ boolOp "<=" x y
jsOp (EQ ty) [x, y] = pure $ boolOp "===" x y
jsOp (GTE ty) [x, y] = pure $ boolOp ">=" x y
jsOp (GT ty) [x, y] = pure $ boolOp ">" x y
jsOp StrLength [x] = pure $ toBigInt $ x <+> ".length"
jsOp StrHead [x] = pure $ "(" <+> x <+> ".charAt(0))"
jsOp StrTail [x] = pure $ "(" <+> x <+> ".slice(1))"
jsOp StrIndex [x, y] = pure $ "(" <+> x <+> ".charAt(" <+> fromBigInt y <+> "))"
jsOp StrCons [x, y] = pure $ binOp "+" x y
jsOp StrAppend [x, y] = pure $ binOp "+" x y
jsOp StrReverse [x] = pure $ callFun1 (esName "strReverse") x
jsOp StrSubstr [offset, len, str] =
  let o = fromBigInt offset
   in pure $ hcat [str,".slice(",o,",",o,"+",fromBigInt len,")"]
jsOp DoubleExp [x]     = pure $ callFun1 "Math.exp" x
jsOp DoubleLog [x]     = pure $ callFun1 "Math.log" x
jsOp DoubleSin [x]     = pure $ callFun1 "Math.sin" x
jsOp DoubleCos [x]     = pure $ callFun1 "Math.cos" x
jsOp DoubleTan [x]     = pure $ callFun1 "Math.tan" x
jsOp DoubleASin [x]    = pure $ callFun1 "Math.asin" x
jsOp DoubleACos [x]    = pure $ callFun1 "Math.acos" x
jsOp DoubleATan [x]    = pure $ callFun1 "Math.atan" x
jsOp DoubleSqrt [x]    = pure $ callFun1 "Math.sqrt" x
jsOp DoubleFloor [x]   = pure $ callFun1 "Math.floor" x
jsOp DoubleCeiling [x] = pure $ callFun1 "Math.ceil" x

jsOp (Cast StringType DoubleType) [x] = pure $ jsNumberOfString x
jsOp (Cast ty StringType) [x] = pure $ jsAnyToString x
jsOp (Cast ty ty2) [x]        = castInt ty ty2 x
jsOp BelieveMe [_,_,x] = pure x
jsOp (Crash) [_, msg] = pure $ jsCrashExp msg

readCCPart : String -> (String, String)
readCCPart = breakDrop1 ':'

searchForeign : List String -> List String -> Either (List String) String
searchForeign prefixes xs =
  let pairs = map readCCPart xs
      backends = Left $ map fst pairs
   in maybe backends (Right. snd) $ find ((`elem` prefixes) . fst) pairs

makeForeign :  {auto d : Ref Ctxt Defs}
            -> {auto c : Ref ESs ESSt}
            -> Name
            -> String
            -> Core Doc
makeForeign n x = do
  nd <- var <$> getOrRegisterRef n
  let (ty, def) = readCCPart x
  case ty of
    "lambda" => pure . constant nd . paren $ Text def
    "support" => do
      let (name, lib) = breakDrop1 ',' def
      lib_code <- readDataFile ("js/" ++ lib ++ ".js")
      addToPreamble lib lib_code
      pure . constant nd . Text $ lib ++ "_" ++ name
    "stringIterator" =>
      case def of
        "new"      => pure $ constant nd "__prim_stringIteratorNew"
        "next"     => pure $ constant nd "__prim_stringIteratorNext"
        "toString" => pure $ constant nd "__prim_stringIteratorToString"
        _ => errorConcat
               [ "Invalid string iterator function: ", def, ". "
               , "Supported functions are: "
               , stringList ["new","next","toString"], "."
               ]

    _ => errorConcat
           [ "Invalid foreign type : ", ty, ". "
           , "Supported types are: "
           , stringList ["lambda", "support", "stringIterator"]
           ]

export
foreignDecl :  {auto d : Ref Ctxt Defs}
            -> {auto c : Ref ESs ESSt}
            -> Name
            -> List String
            -> Core Doc
foreignDecl n ccs = do
  tys <- ccTypes <$> get ESs
  case searchForeign tys ccs of
    Right x        => makeForeign n x
    Left  backends =>
      errorConcat
        [ "No supported backend found in the definition of ", show n, ". "
        , "Supported backends: ", stringList tys, ". "
        , "Backends in definition: ", stringList backends, "."
        ]

export
jsPrim : {auto c : Ref ESs ESSt} -> Name -> List Doc -> Core Doc
jsPrim (NS _ (UN "prim__newIORef")) [_,v,_] = pure $ hcat ["({value:", v, "})"]
jsPrim (NS _ (UN "prim__readIORef")) [_,r,_] = pure $ hcat ["(", r, ".value)"]
jsPrim (NS _ (UN "prim__writeIORef")) [_,r,v,_] = pure $ hcat ["(", r, ".value=", v, ")"]
jsPrim (NS _ (UN "prim__newArray")) [_,s,v,_] = pure $ hcat ["(Array(Number(", s, ")).fill(", v, "))"]
jsPrim (NS _ (UN "prim__arrayGet")) [_,x,p,_] = pure $ hcat ["(", x, "[", p, "])"]
jsPrim (NS _ (UN "prim__arraySet")) [_,x,p,v,_] = pure $ hcat ["(", x, "[", p, "]=", v, ")"]
jsPrim (NS _ (UN "prim__os")) [] = pure $ Text $ esName "sysos"
jsPrim (NS _ (UN "void")) [_, _] = pure . jsCrashExp $ jsStringDoc "Error: Executed 'void'"
jsPrim (NS _ (UN "prim__void")) [_, _] = pure . jsCrashExp $ jsStringDoc "Error: Executed 'void'"
jsPrim (NS _ (UN "prim__codegen")) [] = do
    (cg :: _) <- ccTypes <$> get ESs
        | _ => pure "\"javascript\""
    pure . Text $ jsString cg
jsPrim x args = throw $ InternalError $ "prim not implemented: " ++ (show x)

isArg : CGMode -> Exp -> Bool
isArg Pretty (ELam _ $ _ :: _)                       = False
isArg Pretty (ELam _ $ Result $ ConSwitch _ _ _ _)   = False
isArg Pretty (ELam _ $ Result $ ConstSwitch _ _ _ _) = False
isArg _      _                                       = True

isFun : Exp -> Bool
isFun (ELam _ _) = False
isFun _          = True

break : Effect -> Doc -> Doc
break Returns          d = d
break (ErrorWithout _) d = vcat [d, "break;"]

switch :  (scrutinee : Doc)
       -> (alts : List (Doc,Doc))
       -> (def : Maybe Doc)
       -> Doc
switch sc alts def =
  let stmt    = "switch" <+> paren sc <+> SoftSpace
      defcase = concatMap (pure . anyCase "default") def
   in stmt <+> block (vcat $ map alt alts ++ defcase)

  where anyCase : Doc -> Doc -> Doc
        anyCase s d =
          let b = if isMultiline d then block d else d
           in s <+> softColon <+> b

        alt : (Doc,Doc) -> Doc
        alt (e,d) = anyCase ("case" <++> e) d

lambdaArgs : List Var -> Doc
lambdaArgs [] = "()" <+> lambdaArrow
lambdaArgs xs = hcat $ (<+> lambdaArrow) . var <$> xs

mutual
  exp : {auto c : Ref ESs ESSt} -> Exp -> Core Doc
  exp (EMinimal x) = pure $ minimal x
  exp (ELam xs (Result $ Return $ y@(ECon _ _ _))) =
     map (\e => lambdaArgs xs <+> paren e) (exp y)
  exp (ELam xs (Result $ Return $ y)) = (lambdaArgs xs <+> ) <$> exp y
  exp (ELam xs y) = (lambdaArgs xs <+>) . block <$> block y
  exp (EApp x xs) = do
    o    <- exp x
    args <- traverse exp xs
    pure $ app o args

  exp (ECon tag ci xs) = applyCon tag <$> traverse exp xs

  exp (EOp x xs) = traverseVect exp xs >>= jsOp x
  exp (EExtPrim x xs) = traverse exp xs >>= jsPrim x
  exp (EPrimVal x) = Text <$> jsConstant x
  exp EErased = pure "undefined"

  stmt : {e : _} -> {auto c : Ref ESs ESSt} -> Stmt e -> Core Doc
  stmt (Return y) = (\e => "return" <++> e <+> ";") <$> exp y
  stmt (Const v x) = constant (var v) <$> exp x
  stmt (Declare v s) =
    (\d => vcat ["let" <++> var v <+> ";",d]) <$> stmt s
  stmt (Assign v x) =
    (\d => var v <+> softEq <+> d <+> ";") <$> exp x

  stmt (ConSwitch r sc alts def) = do
    as <- traverse alt alts
    d  <- traverseOpt block def
    pure $  switch (minimal sc <+> ".h") as d
    where alt : EConAlt r -> Core (Doc,Doc)
          alt (MkEConAlt t _ b) = (tag2es t,) <$> block b

  stmt (ConstSwitch r sc alts def) = do
    as <- traverse alt alts
    d  <- traverseOpt block def
    ex <- exp sc
    pure $ switch ex as d
    where alt : EConstAlt r -> Core (Doc,Doc)
          alt (MkEConstAlt c b) = do d    <- block b
                                     cnst <- jsConstant c
                                     pure (Text cnst, d)

  stmt (Error x) = pure . jsCrashExp $ jsStringDoc x

  block : {e : _} -> {auto c : Ref ESs ESSt} -> Block e -> Core Doc
  block = map vcat . go
    where go : Block e -> Core (List $ Doc)
          go (Result x) = pure . break e <$> stmt x
          go (h :: t)   = [| stmt h :: go t |]

printDoc : CGMode -> Doc -> String
printDoc Pretty y = pretty (y <+> LineBreak)
printDoc Compact y = compact y
printDoc Minimal y = compact y

def : {auto c : Ref ESs ESSt} -> Function -> Core String
def (MkFunction n as body) = do
  reset
  ref  <- getOrRegisterRef n
  args <- traverse registerLocal as
  mde  <- mode <$> get ESs
  b    <- block Returns body >>= block
  pure $ printDoc mde $ function (var ref) (map var args) b

foreign :  {auto c : Ref ESs ESSt}
        -> {auto d : Ref Ctxt Defs}
        -> (Name,FC,NamedDef)
        -> Core (List String)
foreign (n, _, MkNmForeign path _ _) = pure . pretty <$> foreignDecl n path
foreign _                            = pure []

tailRec : Name
tailRec = UN "__tailRec"

export
compileToES : Ref Ctxt Defs -> ClosedTerm -> List String -> Core String
compileToES c tm ccTypes = do
  cdata <- getCompileData False Cases tm
  directives <- getDirectives Node
  let mode = if "minimal" `elem` directives then Minimal
             else if "compact" `elem` directives then Compact
             else Pretty
  s <- newRef ESs $ init mode (isArg mode) isFun ccTypes
  addRef tailRec (VName tailRec)
  let allDefs =  (mainExpr, EmptyFC, MkNmFun [] $ forget cdata.mainExpr)
              :: cdata.namedDefs
      defs    = functions tailRec allDefs
  defDecls <- traverse def defs
  foreigns <- concat <$> traverse foreign allDefs
  mainName <- compact . var <$> getOrRegisterRef mainExpr
  let main = "try{" ++ mainName ++ "()}catch(e){if(e instanceof IdrisError){console.log('ERROR: ' + e.message)}else{throw e} }"
      allDecls = fastUnlines $ foreigns ++ defDecls
  st <- get ESs
  static_preamble <- readDataFile ("js/support.js")
  let pre = showSep "\n" $ static_preamble :: (values $ preamble st)
  pure $ fastUnlines [pre,allDecls,main]

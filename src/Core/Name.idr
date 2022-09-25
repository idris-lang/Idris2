module Core.Name

import Data.Maybe
import Data.String
import Decidable.Equality
import Libraries.Data.String.Extra
import Libraries.Text.PrettyPrint.Prettyprinter
import Libraries.Text.PrettyPrint.Prettyprinter.Util
import Libraries.Utils.String

import public Core.Name.Namespace

%default total

public export
data Fixity = InfixL | InfixR | Infix | Prefix

export
Show Fixity where
  show InfixL = "infixl"
  show InfixR = "infixr"
  show Infix  = "infix"
  show Prefix = "prefix"

public export
record Operator where
  constructor MkOperator
  opFixity : Fixity
  opLevel  : Nat
  opSyntax : String

%name Operator op

||| A username has some structure
public export
data UserName : Type where
  Basic      : String -> UserName   -- default name constructor       e.g. map
  Op         : Operator -> UserName -- operator                       e.g. <><
  Field      : String -> UserName   -- field accessor                 e.g. .fst
  Underscore : UserName             -- no name                        e.g. _

%name UserName un

export
isOpChar : Char -> Bool
isOpChar c = c `elem` (unpack ":!#$%&*+./<=>?@\\^|-~")

export
||| Test whether a user name begins with an operator symbol.
isOpString : String -> Bool
isOpString n = fromMaybe False $ do
   c <- fst <$> strUncons n
   guard (isOpChar c)
   pure True

export
isOpUserName : UserName -> Bool
isOpUserName (Op _) = True
isOpUserName _ = False

||| A smart constructor taking a string and parsing it as the appropriate
||| username
export
mkUserName : String -> UserName
mkUserName "_" = Underscore
mkUserName str with (strM str)
  mkUserName _   | StrCons '.' n = Field n
  mkUserName str | _
    = ifThenElse (isOpString str)
        (Op (MkOperator Infix 20 str)) -- arbitrary
        (Basic str)

||| Name helps us track a name's structure as well as its origin:
||| was it user-provided or machine-manufactured? For what reason?
public export
data Name : Type where
     NS : Namespace -> Name -> Name -- in a namespace
     UN : UserName -> Name -- user defined name
     MN : String -> Int -> Name -- machine generated name
     PV : Name -> Int -> Name -- pattern variable name; int is the resolved function id
     DN : String -> Name -> Name -- a name and how to display it
     Nested : (Int, Int) -> Name -> Name -- nested function name
     CaseBlock : String -> Int -> Name -- case block nested in (resolved) name
     WithBlock : String -> Int -> Name -- with block nested in (resolved) name
     Resolved : Int -> Name -- resolved, index into context

%name Name n

export
mkNamespacedName : Maybe Namespace -> UserName -> Name
mkNamespacedName Nothing nm = UN nm
mkNamespacedName (Just ns) nm = NS ns (UN nm)

||| `matches a b` checks that the name `a` matches `b` assuming
||| the name roots are already known to be matching.
||| For instance, both `reverse` and `List.reverse` match the fully
||| qualified name `Data.List.reverse`.
export
matches : Name -> Name -> Bool
matches (NS ns _) (NS cns _) = isApproximationOf ns cns
matches (NS _ _) _
  -- gallais: I don't understand this case but that's what was there.
  = True -- no in library name, so root doesn't match
matches _ _ = True -- no prefix, so root must match, so good

-- Update a name imported with 'import as', for creating an alias
export
asName : ModuleIdent -> -- Initial module name
         Namespace -> -- 'as' module name
         Name -> -- identifier
         Name
asName old new (DN s n) = DN s (asName old new n)
asName old new (NS ns n)
    = NS (replace old new ns) n
asName _ _ n = n

export
userNameRoot : Name -> Maybe UserName
userNameRoot (NS _ n) = userNameRoot n
userNameRoot (UN n) = Just n
userNameRoot (DN _ n) = userNameRoot n
userNameRoot _ = Nothing

export
||| Test whether a name begins with an operator symbol.
isOpName : Name -> Bool
isOpName = maybe False isOpUserName . userNameRoot

export
isUnderscoreName : Name -> Bool
isUnderscoreName (UN Underscore) = True
isUnderscoreName (MN "_" _) = True
isUnderscoreName _ = False

export
isPatternVariable : UserName -> Bool
isPatternVariable (Basic nm) = lowerFirst nm
isPatternVariable (Op _) = False
isPatternVariable (Field _) = False
isPatternVariable Underscore = True

export
isUserName : Name -> Bool
isUserName (PV _ _) = False
isUserName (MN _ _) = False
isUserName (NS _ n) = isUserName n
isUserName (DN _ n) = isUserName n
isUserName _ = True

||| True iff name can be traced back to a source name.
||| Used to determine whether it needs semantic highlighting.
export
isSourceName : Name -> Bool
isSourceName (NS _ n) = isSourceName n
isSourceName (UN _) = True
isSourceName (MN _ _) = False
isSourceName (PV n _) = isSourceName n
isSourceName (DN _ n) = isSourceName n
isSourceName (Nested _ n) = isSourceName n
isSourceName (CaseBlock _ _) = False
isSourceName (WithBlock _ _) = False
isSourceName (Resolved _) = False

export
isRF : Name -> Maybe (Namespace, String)
isRF (NS ns n) = map (mapFst (ns <.>)) (isRF n)
isRF (UN (Field n)) = Just (emptyNS, n)
isRF _ = Nothing

export
isUN : Name -> Maybe (Namespace, UserName)
isUN (UN un) = Just (emptyNS, un)
isUN (NS ns n) = map (mapFst (ns <.>)) (isUN n)
isUN _ = Nothing

export
isBasic : UserName -> Maybe String
isBasic (Basic str) = Just str
isBasic _ = Nothing

export
isOp : UserName -> Maybe Operator
isOp (Op op) = Just op
isOp _ = Nothing

export
isField : UserName -> Maybe String
isField (Field str) = Just str
isField _ = Nothing

export
displayUserName : UserName -> String
displayUserName (Basic n) = n
displayUserName (Op op) = op.opSyntax
displayUserName (Field n) = n
displayUserName Underscore = "_"

export
nameRoot : Name -> String
nameRoot (NS _ n) = nameRoot n
nameRoot (UN n) = displayUserName n
nameRoot (MN n _) = n
nameRoot (PV n _) = nameRoot n
nameRoot (DN _ n) = nameRoot n
nameRoot (Nested _ inner) = nameRoot inner
nameRoot (CaseBlock n _) = "$" ++ show n
nameRoot (WithBlock n _) = "$" ++ show n
nameRoot (Resolved i) = "$" ++ show i

export
displayName : Name -> (Maybe Namespace, String)
displayName (NS ns n) = mapFst (pure . maybe ns (ns <.>)) $ displayName n
displayName (UN n) = (Nothing, displayUserName n)
displayName (MN n _) = (Nothing, n)
displayName (PV n _) = displayName n
displayName (DN n _) = (Nothing, n)
displayName (Nested _ n) = displayName n
displayName (CaseBlock outer _) = (Nothing, "case block in " ++ show outer)
displayName (WithBlock outer _) = (Nothing, "with block in " ++ show outer)
displayName (Resolved i) = (Nothing, "$resolved" ++ show i)

export
splitNS : Name -> (Namespace, Name)
splitNS (NS ns nm) = mapFst (ns <.>) (splitNS nm)
splitNS nm = (emptyNS, nm)

--- Drop a namespace from a name
export
dropNS : Name -> Name
dropNS (NS _ n) = n
dropNS n = n

-- Drop all of the namespaces from a name
export
dropAllNS : Name -> Name
dropAllNS (NS _ n) = dropAllNS n
dropAllNS n = n

export
mbApplyNS : Maybe Namespace -> Name -> Name
mbApplyNS Nothing n = n
mbApplyNS (Just ns) n = NS ns n

export
isUnsafeBuiltin : Name -> Bool
isUnsafeBuiltin nm = case splitNS nm of
  (ns, UN (Basic str)) =>
       (ns == builtinNS || ns == emptyNS)
    && any {t = List} id
           [ "assert_" `isPrefixOf` str
           , str `elem` [ "prim__believe_me", "believe_me"
                        , "prim__crash", "idris_crash"
                        ]
           ]
  _ => False

export
Show UserName where
  show (Basic n) = n
  show (Op op) = op .opSyntax
  show (Field n) = "." ++ n
  show Underscore = "_"

export
Show Name where
  show (NS ns n@(UN (Field _))) = show ns ++ ".(" ++ show n ++ ")"
  show (NS ns n) = show ns ++ "." ++ show n
  show (UN x) = show x
  show (MN x y) = "{" ++ x ++ ":" ++ show y ++ "}"
  show (PV n d) = "{P:" ++ show n ++ ":" ++ show d ++ "}"
  show (DN str n) = str
  show (Nested (outer, idx) inner)
      = show outer ++ ":" ++ show idx ++ ":" ++ show inner
  show (CaseBlock outer i) = "case block in " ++ outer
  show (WithBlock outer i) = "with block in " ++ outer
  show (Resolved x) = "$resolved" ++ show x

export
[RawOP] Show Operator where
  showPrec d (MkOperator f l op)
    = showCon d "MkOperator"
    $ showArg f ++ showArg l ++ showArg op

export
[RawUN] Show UserName where
  showPrec d (Basic n) = showCon d "Basic" $ showArg n
  showPrec d (Op op) = showCon d "Op" $ showArg @{RawOP} op
  showPrec d (Field n) = showCon d "Field" $ showArg n
  showPrec d Underscore = "Underscore"

export
covering
[Raw] Show Name where
  showPrec d (NS ns n) = showCon d "NS" $ showArg ns ++ showArg n
  showPrec d (UN x) = showCon d "UN" $ showArg @{RawUN} x
  showPrec d (MN x y) = showCon d "MN" $ showArg x ++ showArg y
  showPrec d (PV n i) = showCon d "PV" $ showArg n ++ showArg i
  showPrec d (DN str n) = showCon d "DN" $ showArg str ++ showArg n
  showPrec d (Nested ij n) = showCon d "Nested" $ showArg ij ++ showArg n
  showPrec d (CaseBlock str i) = showCon d "CaseBlock" $ showArg str ++ showArg i
  showPrec d (WithBlock str i) = showCon d "WithBlock" $ showArg str ++ showArg i
  showPrec d (Resolved i) = showCon d "Resolved" $ showArg i

export
Pretty Void UserName where
  pretty (Basic n) = pretty n
  pretty (Op op) = pretty op.opSyntax
  pretty (Field n) = "." <+> pretty n
  pretty Underscore = "_"

isPrettyOpUN : Bool -> UserName -> Bool
isPrettyOpUN b (Field _) = b -- prefixed fields need to be parenthesised
isPrettyOpUN b (Op _) = True
isPrettyOpUN b _ = False

export
||| Will it be an operation once prettily displayed?
||| The first boolean states whether the operator is prefixed.
isPrettyOp : Bool -> Name -> Bool
isPrettyOp b (UN un) = isPrettyOpUN b un
isPrettyOp b (DN str _) = isPrettyOpUN b (mkUserName str)
isPrettyOp b nm = False

mutual

  export
  covering
  prettyOp : Bool -> Name -> Doc Void
  prettyOp b nm = parenthesise (isPrettyOp b nm) (pretty nm)

  export
  covering
  Pretty Void Name where
    pretty (NS ns n) = pretty ns <+> dot <+> prettyOp True n
    pretty (UN x) = pretty x
    pretty (MN x y) = braces (pretty x <+> colon <+> byShow y)
    pretty (PV n d) = braces (pretty 'P' <+> colon <+> pretty n <+> colon <+> byShow d)
    pretty (DN str _) = pretty str
    pretty (Nested (outer, idx) inner)
      = byShow outer <+> colon <+> byShow idx <+> colon <+> pretty inner
    pretty (CaseBlock outer _) = reflow "case block in" <++> pretty outer
    pretty (WithBlock outer _) = reflow "with block in" <++> pretty outer
    pretty (Resolved x) = pretty "$resolved" <+> pretty (show x)

export
Eq Fixity where
  InfixL == InfixL = True
  InfixR == InfixR = True
  Infix == Infix = True
  Prefix == Prefix = True
  _ == _ = False

export
Eq Operator where
  MkOperator f l s == MkOperator f' l' s'
    = s == s' && f == f' && l == l'

export
Eq UserName where
  (==) (Basic x) (Basic y) = x == y
  (==) (Op x) (Op y) = x == y
  (==) (Field x) (Field y) = x == y
  (==) Underscore Underscore = True
  (==) _ _ = False

export
Eq Name where
    (==) (NS ns n) (NS ns' n') = n == n' && ns == ns'
    (==) (UN x) (UN y) = x == y
    (==) (MN x y) (MN x' y') = y == y' && x == x'
    (==) (PV x y) (PV x' y') = x == x' && y == y'
    (==) (DN _ n) (DN _ n') = n == n'
    (==) (Nested x y) (Nested x' y') = x == x' && y == y'
    (==) (CaseBlock x y) (CaseBlock x' y') = y == y' && x == x'
    (==) (WithBlock x y) (WithBlock x' y') = y == y' && x == x'
    (==) (Resolved x) (Resolved x') = x == x'
    (==) _ _ = False

usernameTag : UserName -> Int
usernameTag (Basic _) = 0
usernameTag (Op _) = 1
usernameTag (Field _) = 2
usernameTag Underscore = 3

export
fixityTag : Fixity -> Int
fixityTag InfixL = 0
fixityTag InfixR = 1
fixityTag Infix = 2
fixityTag Prefix = 3

export
tagFixity : Int -> Maybe Fixity
tagFixity 0 = pure InfixL
tagFixity 1 = pure InfixR
tagFixity 2 = pure Infix
tagFixity 3 = pure Prefix
tagFixity _ = Nothing

export
Ord Fixity where
  compare x y = compare (fixityTag x) (fixityTag y)

export
Ord Operator where
  compare (MkOperator f l s) (MkOperator f' l' s') =
    case compare s s' of
      EQ => case compare f f' of
        EQ => compare l l'
        res => res
      res => res

export
Ord UserName where
  compare (Basic x) (Basic y) = compare x y
  compare (Op x) (Op y) = compare x y
  compare (Field x) (Field y) = compare x y
  compare Underscore Underscore = EQ
  compare x y = compare (usernameTag x) (usernameTag y)

nameTag : Name -> Int
nameTag (NS _ _) = 0
nameTag (UN _) = 1
nameTag (MN _ _) = 2
nameTag (PV _ _) = 3
nameTag (DN _ _) = 4
nameTag (Nested _ _) = 6
nameTag (CaseBlock _ _) = 7
nameTag (WithBlock _ _) = 8
nameTag (Resolved _) = 9

export
Ord Name where
    compare (NS x y) (NS x' y')
        = case compare y y' of -- Compare base name first (more likely to differ)
               EQ => compare x x'
               -- Because of the terrible way Idris 1 compiles 'case', this
               -- is actually faster than just having 't => t'...
               GT => GT
               LT => LT
    compare (UN x) (UN y) = compare x y
    compare (MN x y) (MN x' y')
        = case compare y y' of
               EQ => compare x x'
               GT => GT
               LT => LT
    compare (PV x y) (PV x' y')
        = case compare y y' of
               EQ => compare x x'
               GT => GT
               LT => LT
    compare (DN _ n) (DN _ n') = compare n n'
    compare (Nested x y) (Nested x' y')
        = case compare y y' of
               EQ => compare x x'
               GT => GT
               LT => LT
    compare (CaseBlock x y) (CaseBlock x' y')
        = case compare y y' of
               EQ => compare x x'
               GT => GT
               LT => LT
    compare (WithBlock x y) (WithBlock x' y')
        = case compare y y' of
               EQ => compare x x'
               GT => GT
               LT => LT
    compare (Resolved x) (Resolved y) = compare x y

    compare x y = compare (nameTag x) (nameTag y)

export
DecEq Fixity where
  decEq InfixL InfixL = Yes Refl
  decEq InfixL InfixR = No (\case prf impossible)
  decEq InfixL Infix = No (\case prf impossible)
  decEq InfixL Prefix = No (\case prf impossible)
  decEq InfixR InfixL = No (\case prf impossible)
  decEq InfixR InfixR = Yes Refl
  decEq InfixR Infix = No (\case prf impossible)
  decEq InfixR Prefix = No (\case prf impossible)
  decEq Infix InfixL = No (\case prf impossible)
  decEq Infix InfixR = No (\case prf impossible)
  decEq Infix Infix = Yes Refl
  decEq Infix Prefix = No (\case prf impossible)
  decEq Prefix InfixL = No (\case prf impossible)
  decEq Prefix InfixR = No (\case prf impossible)
  decEq Prefix Infix = No (\case prf impossible)
  decEq Prefix Prefix = Yes Refl

export
DecEq Operator where
  decEq (MkOperator f l s) (MkOperator f' l' s') with (decEq f f')
    _ | No nprf = No (nprf . cong opFixity)
    _ | Yes prf with (decEq l l')
      _ | No nprl = No (nprl . cong opLevel)
      _ | Yes prl with (decEq s s')
        _ | No nprs = No (nprs . cong opSyntax)
        _ | Yes prs = Yes (rewrite prf in rewrite prl in rewrite prs in Refl)

export
userNameEq : (x, y : UserName) -> Maybe (x = y)
userNameEq (Basic x) (Basic y) with (decEq x y)
  userNameEq (Basic x) (Basic y) | Yes prf = Just (cong Basic prf)
  userNameEq (Basic x) (Basic y) | No nprf = Nothing
userNameEq (Op x) (Op y) with (decEq x y)
  userNameEq (Op x) (Op y) | Yes prf = Just (cong Op prf)
  userNameEq (Op x) (Op y) | No nprf = Nothing
userNameEq (Field x) (Field y) with (decEq x y)
  userNameEq (Field x) (Field y) | Yes prf = Just (cong Field prf)
  userNameEq (Field x) (Field y) | No nprf = Nothing
userNameEq Underscore Underscore = Just Refl
userNameEq _ _ = Nothing


export
nameEq : (x : Name) -> (y : Name) -> Maybe (x = y)
nameEq (NS xs x) (NS ys y) with (decEq xs ys)
  nameEq (NS ys x) (NS ys y) | (Yes Refl) with (nameEq x y)
    nameEq (NS ys x) (NS ys y) | (Yes Refl) | Nothing = Nothing
    nameEq (NS ys y) (NS ys y) | (Yes Refl) | (Just Refl) = Just Refl
  nameEq (NS xs x) (NS ys y) | (No contra) = Nothing
nameEq (UN x) (UN y) = map (cong UN) (userNameEq x y)
nameEq (MN x t) (MN x' t') with (decEq x x')
  nameEq (MN x t) (MN x t') | (Yes Refl) with (decEq t t')
    nameEq (MN x t) (MN x t) | (Yes Refl) | (Yes Refl) = Just Refl
    nameEq (MN x t) (MN x t') | (Yes Refl) | (No contra) = Nothing
  nameEq (MN x t) (MN x' t') | (No contra) = Nothing
nameEq (PV x t) (PV y t') with (nameEq x y)
  nameEq (PV y t) (PV y t') | (Just Refl) with (decEq t t')
    nameEq (PV y t) (PV y t) | (Just Refl) | (Yes Refl) = Just Refl
    nameEq (PV y t) (PV y t') | (Just Refl) | (No p) = Nothing
  nameEq (PV x t) (PV y t') | Nothing = Nothing
nameEq (DN x t) (DN y t') with (decEq x y)
  nameEq (DN y t) (DN y t') | (Yes Refl) with (nameEq t t')
    nameEq (DN y t) (DN y t) | (Yes Refl) | (Just Refl) = Just Refl
    nameEq (DN y t) (DN y t') | (Yes Refl) | Nothing = Nothing
  nameEq (DN x t) (DN y t') | (No p) = Nothing
nameEq (Nested x y) (Nested x' y') with (decEq x x')
  nameEq (Nested x y) (Nested x' y') | (No p) = Nothing
  nameEq (Nested x y) (Nested x y') | (Yes Refl) with (nameEq y y')
    nameEq (Nested x y) (Nested x y') | (Yes Refl) | Nothing = Nothing
    nameEq (Nested x y) (Nested x y) | (Yes Refl) | (Just Refl) = Just Refl
nameEq (CaseBlock x y) (CaseBlock x' y') with (decEq x x')
  nameEq (CaseBlock x y) (CaseBlock x' y') | (No p) = Nothing
  nameEq (CaseBlock x y) (CaseBlock x y') | (Yes Refl) with (decEq y y')
    nameEq (CaseBlock x y) (CaseBlock x y') | (Yes Refl) | (No p) = Nothing
    nameEq (CaseBlock x y) (CaseBlock x y) | (Yes Refl) | (Yes Refl) = Just Refl
nameEq (WithBlock x y) (WithBlock x' y') with (decEq x x')
  nameEq (WithBlock x y) (WithBlock x' y') | (No p) = Nothing
  nameEq (WithBlock x y) (WithBlock x y') | (Yes Refl) with (decEq y y')
    nameEq (WithBlock x y) (WithBlock x y') | (Yes Refl) | (No p) = Nothing
    nameEq (WithBlock x y) (WithBlock x y) | (Yes Refl) | (Yes Refl) = Just Refl
nameEq (Resolved x) (Resolved y) with (decEq x y)
  nameEq (Resolved y) (Resolved y) | (Yes Refl) = Just Refl
  nameEq (Resolved x) (Resolved y) | (No contra) = Nothing
nameEq _ _ = Nothing

export
namesEq : (xs : List Name) -> (ys : List Name) -> Maybe (xs = ys)
namesEq [] [] = Just Refl
namesEq (x :: xs) (y :: ys)
    = do p <- nameEq x y
         ps <- namesEq xs ys
         rewrite p
         rewrite ps
         Just Refl
namesEq _ _ = Nothing

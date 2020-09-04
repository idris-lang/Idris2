module Core.Name

import Data.List
import Data.Strings
import Decidable.Equality
import Text.PrettyPrint.Prettyprinter
import Text.PrettyPrint.Prettyprinter.Util

import public Core.Name.Namespace

%default total

||| Name helps us track a name's structure as well as its origin:
||| was it user-provided or machine-manufactured? For what reason?
public export
data Name : Type where
     NS : Namespace -> Name -> Name -- in a namespace
     UN : String -> Name -- user defined name
     MN : String -> Int -> Name -- machine generated name
     PV : Name -> Int -> Name -- pattern variable name; int is the resolved function id
     DN : String -> Name -> Name -- a name and how to display it
     Nested : (Int, Int) -> Name -> Name -- nested function name
     CaseBlock : String -> Int -> Name -- case block nested in (resolved) name
     WithBlock : String -> Int -> Name -- with block nested in (resolved) name
     Resolved : Int -> Name -- resolved, index into context

export
mkNamespacedName : Maybe Namespace -> String -> Name
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
userNameRoot : Name -> Maybe String
userNameRoot (NS _ n) = userNameRoot n
userNameRoot (UN n) = Just n
userNameRoot (DN _ n) = userNameRoot n
userNameRoot _ = Nothing

export
isUserName : Name -> Bool
isUserName (PV _ _) = False
isUserName (MN _ _) = False
isUserName (NS _ n) = isUserName n
isUserName (DN _ n) = isUserName n
isUserName _ = True

export
nameRoot : Name -> String
nameRoot (NS _ n) = nameRoot n
nameRoot (UN n) = n
nameRoot (MN n _) = n
nameRoot (PV n _) = nameRoot n
nameRoot (DN _ n) = nameRoot n
nameRoot (Nested _ inner) = nameRoot inner
nameRoot (CaseBlock n _) = "$" ++ show n
nameRoot (WithBlock n _) = "$" ++ show n
nameRoot (Resolved i) = "$" ++ show i

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
Show Name where
  show (NS ns n) = show ns ++ "." ++ show n
  show (UN x) = x
  show (MN x y) = "{" ++ x ++ ":" ++ show y ++ "}"
  show (PV n d) = "{P:" ++ show n ++ ":" ++ show d ++ "}"
  show (DN str n) = str
  show (Nested (outer, idx) inner)
      = show outer ++ ":" ++ show idx ++ ":" ++ show inner
  show (CaseBlock outer i) = "case block in " ++ outer
  show (WithBlock outer i) = "with block in " ++ outer
  show (Resolved x) = "$resolved" ++ show x

export
Pretty Name where
  pretty (NS ns n) = pretty ns <+> dot <+> pretty n
  pretty (UN x) = pretty x
  pretty (MN x y) = braces (pretty x <+> colon <+> pretty y)
  pretty (PV n d) = braces (pretty 'P' <+> colon <+> pretty n <+> colon <+> pretty d)
  pretty (DN str _) = pretty str
  pretty (Nested (outer, idx) inner) = pretty outer <+> colon <+> pretty idx <+> colon <+> pretty inner
  pretty (CaseBlock outer _) = reflow "case block in" <++> pretty outer
  pretty (WithBlock outer _) = reflow "with block in" <++> pretty outer
  pretty (Resolved x) = pretty "$resolved" <+> pretty x

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

nameTag : Name -> Int
nameTag (NS _ _) = 0
nameTag (UN _) = 1
nameTag (MN _ _) = 2
nameTag (PV _ _) = 3
nameTag (DN _ _) = 4
nameTag (Nested _ _) = 5
nameTag (CaseBlock _ _) = 6
nameTag (WithBlock _ _) = 7
nameTag (Resolved _) = 8

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
nameEq : (x : Name) -> (y : Name) -> Maybe (x = y)
nameEq (NS xs x) (NS ys y) with (decEq xs ys)
  nameEq (NS ys x) (NS ys y) | (Yes Refl) with (nameEq x y)
    nameEq (NS ys x) (NS ys y) | (Yes Refl) | Nothing = Nothing
    nameEq (NS ys y) (NS ys y) | (Yes Refl) | (Just Refl) = Just Refl
  nameEq (NS xs x) (NS ys y) | (No contra) = Nothing
nameEq (UN x) (UN y) with (decEq x y)
  nameEq (UN y) (UN y) | (Yes Refl) = Just Refl
  nameEq (UN x) (UN y) | (No contra) = Nothing
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

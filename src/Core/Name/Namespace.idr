module Core.Name.Namespace

import Data.List
import Data.List1
import Data.Strings
import Decidable.Equality
import Text.PrettyPrint.Prettyprinter
import Text.PrettyPrint.Prettyprinter.Util

%default total

-------------------------------------------------------------------------------------
-- TYPES
-------------------------------------------------------------------------------------

||| Nested namespaces are stored in reverse order.
||| i.e. `X.Y.Z.foo` will be represented as `NS [Z,Y,X] foo`
||| As a consequence we hide the representation behind an opaque type alias
||| and force users to manufacture and manipulate namespaces via the safe
||| functions we provide.
export
data Namespace : Type where
  MkNS : List String -> Namespace

||| A Module Identifier is, similarly to a namespace, stored inside out.
export
data ModuleIdent : Type where
  MkMI : List String -> ModuleIdent

||| Sometimes we need to convert a module identifier to the corresponding
||| namespace. It is still useful to have them as distinct types as it
||| clarifies the distinct roles of X.Y.Z as a module name vs. S.T.U as a
||| namespace in `import X.Y.Z as S.T.U`.
export
miAsNamespace : ModuleIdent -> Namespace
miAsNamespace (MkMI mi) = MkNS mi

||| Sometimes we need to convert a namespace to the corresponding
||| module identifier. It is still useful to have them as distinct types as
||| it clarifies the distinct roles of X.Y.Z as a module name vs. S.T.U as a
||| namespace in `import X.Y.Z as S.T.U`.
export
nsAsModuleIdent : Namespace -> ModuleIdent
nsAsModuleIdent (MkNS ns) = MkMI ns

-------------------------------------------------------------------------------------
-- SMART CONSTRUCTORS
-------------------------------------------------------------------------------------

export
mkNamespacedIdent : String -> (Maybe Namespace, String)
mkNamespacedIdent str = case reverse (split (== '.') str) of
  (name ::: []) => (Nothing, name)
  (name ::: ns) => (Just (MkNS ns), name)

export
mkNestedNamespace : Maybe Namespace -> String -> Namespace
mkNestedNamespace Nothing n = MkNS [n]
mkNestedNamespace (Just (MkNS ns)) n = MkNS (n :: ns)

export
mkNamespace : String -> Namespace
mkNamespace ""  = MkNS []
mkNamespace str = uncurry mkNestedNamespace (mkNamespacedIdent str)

export
mkModuleIdent : Maybe Namespace -> String -> ModuleIdent
mkModuleIdent Nothing n = MkMI [n]
mkModuleIdent (Just (MkNS ns)) n = MkMI (n :: ns)

-------------------------------------------------------------------------------------
-- MANIPULATING NAMESPACES
-------------------------------------------------------------------------------------

infixl 5 <.>
||| Extend an existing namespace with additional name parts to form a more local one.
||| e.g. `X.Y.Z <.> S.T.U` to get `X.Y.Z.S.T.U`.
export
(<.>) : (existing, local : Namespace) -> Namespace
(MkNS existing) <.> (MkNS local)
   -- The namespaces are stored in reverse order so the local should end up at
   -- the front of the existing one
   = MkNS (local ++ existing)

export
replace : (old : ModuleIdent) -> (new, ns : Namespace) -> Namespace
replace (MkMI old) (MkNS new) (MkNS ns) = MkNS (go ns) where

  go : List String -> List String
  go [] = []
  go (m :: ms)
        = if old == (m :: ms)
             then new
             else m :: go ms

||| Use at your own risks!
export
unsafeUnfoldNamespace : Namespace -> List String
unsafeUnfoldNamespace (MkNS ns) = ns

export
unsafeFoldNamespace : List String -> Namespace
unsafeFoldNamespace = MkNS

export
unsafeUnfoldModuleIdent : ModuleIdent -> List String
unsafeUnfoldModuleIdent (MkMI ns) = ns

export
unsafeFoldModuleIdent : List String -> ModuleIdent
unsafeFoldModuleIdent = MkMI

-------------------------------------------------------------------------------------
-- HIERARCHICAL STRUCTURE
-------------------------------------------------------------------------------------

-- We don't use the prefix/suffix terminology as it is confusing: are we talking
-- about the namespaces or their representation? Instead our library is structured
-- around the parent/child relation induced by nested namespaces.

||| Nested namespaces naturally give rise to a hierarchical structure. In particular
||| from a given namespace we can compute all of the parent (aka englobing) ones.
||| For instance `allParents Data.List.Properties` should yield a set containing
||| both `Data.List` and `Data` (no guarantee is given on the order).
export
allParents : Namespace -> List Namespace
allParents (MkNS ns) = go ns where

  go : List String -> List Namespace
  go [] = []
  go (n :: ns) = MkNS (n :: ns) :: go ns

||| We can check whether a given namespace is a parent (aka englobing) namespace
||| of a candidate namespace.
||| We expect that `all (\ p => isParentOf p ns) (allParents ns)` holds true.
export
isParentOf : (given, candidate : Namespace) -> Bool
isParentOf (MkNS ms) (MkNS ns)
  -- This is not a typo: namespaces are stored in reverse order so a namespace is
  -- a prefix of another if its reversed list of identifiers is a suffix of that
  -- other's list of identifiers
  = isSuffixOf ms ns

||| When writing qualified names users often do not want to spell out the full
||| namespace, rightly considering that an unambiguous segment should be enough.
||| This function checks whether a candidate is an approximation of a given
||| namespace.
||| We expect `isApproximationOf List.Properties Data.List.Properties` to hold true
||| while `isApproximationOf Data.List Data.List.Properties` should not.
export
isApproximationOf : (given, candidate : Namespace) -> Bool
isApproximationOf (MkNS ms) (MkNS ns)
  -- This is not a typo: namespaces are stored in reverse order so a namespace matches
  -- the end of another if its representation as a list of identifiers is a prefix of
  -- the other's.
  = isPrefixOf ms ns

-------------------------------------------------------------------------------------
-- INSTANCES
-------------------------------------------------------------------------------------

export
Eq Namespace where
  (MkNS ms) == (MkNS ns) = ms == ns

export
Eq ModuleIdent where
  (MkMI ms) == (MkMI ns) = ms == ns

export
Ord Namespace where
    compare (MkNS ms) (MkNS ns) = compare ms ns

mkNSInjective : MkNS ms === MkNS ns -> ms === ns
mkNSInjective Refl = Refl

export
DecEq Namespace where

  decEq (MkNS ms) (MkNS ns) with (decEq ms ns)
    decEq (MkNS ms) (MkNS ns) | No contra = No (contra . mkNSInjective)
    decEq (MkNS ms) (MkNS ns) | Yes eqmsns = Yes (cong MkNS eqmsns)

-- TODO: move somewhere more appropriate
export
showSep : String -> List String -> String
showSep sep [] = ""
showSep sep [x] = x
showSep sep (x :: xs) = x ++ sep ++ showSep sep xs

export
showNSWithSep : String -> Namespace -> String
showNSWithSep sep (MkNS ns) = showSep sep (reverse ns)

export
Show Namespace where
  show = showNSWithSep "."

export
Show ModuleIdent where
  show = showNSWithSep "." . miAsNamespace

export
Pretty Namespace where
  pretty (MkNS ns) = concatWith (surround dot) (pretty <$> reverse ns)

export
Pretty ModuleIdent where
  pretty = pretty . miAsNamespace


-------------------------------------------------------------------------------------
-- CONSTANTS
-------------------------------------------------------------------------------------

||| This is used when evaluating things in the REPL
export
emptyNS : Namespace
emptyNS = mkNamespace ""

export
mainNS : Namespace
mainNS = mkNamespace "Main"

export
partialEvalNS : Namespace
partialEvalNS = mkNamespace "_PE"

export
builtinNS : Namespace
builtinNS = mkNamespace "Builtin"

export
preludeNS : Namespace
preludeNS = mkNamespace "Prelude"

export
typesNS : Namespace
typesNS = mkNamespace "Prelude.Types"

export
basicsNS : Namespace
basicsNS = mkNamespace "Prelude.Basics"

export
eqOrdNS : Namespace
eqOrdNS = mkNamespace "Prelude.EqOrd"

export
primIONS : Namespace
primIONS = mkNamespace "PrimIO"

export
reflectionNS : Namespace
reflectionNS = mkNamespace "Language.Reflection"

export
reflectionTTNS : Namespace
reflectionTTNS = mkNamespace "Language.Reflection.TT"

export
reflectionTTImpNS : Namespace
reflectionTTImpNS = mkNamespace "Language.Reflection.TTImp"

export
dpairNS : Namespace
dpairNS = mkNamespace "Builtin.DPair"

export
natNS : Namespace
natNS = mkNamespace "Data.Nat"

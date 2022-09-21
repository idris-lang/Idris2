module Core.Context.Context

import        Core.Case.CaseTree
import        Core.CompileExpr
import        Core.Env
import public Core.Name
import public Core.Options.Log
import public Core.TT

import Data.IORef
import Data.String

import Libraries.Data.IntMap
import Libraries.Data.IOArray
import Libraries.Data.NameMap
import Libraries.Data.UserNameMap
import Libraries.Utils.Binary
import Libraries.Utils.Scheme

public export
data Ref : (l : label) -> Type -> Type where
     [search l]
     MkRef : IORef a -> Ref x a

public export
data HoleInfo
        = NotHole
        | SolvedHole Nat

public export
record PMDefInfo where
  constructor MkPMDefInfo
  holeInfo : HoleInfo -- data if it comes from a solved hole
  alwaysReduce : Bool -- always reduce, even when quoting etc
                 -- typically for inlinable metavariable solutions
  externalDecl : Bool -- declared in another module, which may affect how it
                      -- is compiled
%name PMDefInfo pminfo

export
defaultPI : PMDefInfo
defaultPI = MkPMDefInfo NotHole False False

public export
record TypeFlags where
  constructor MkTypeFlags
  uniqueAuto : Bool  -- should 'auto' implicits check for uniqueness
  external : Bool -- defined externally (e.g. in a C or Scheme library)

export
defaultFlags : TypeFlags
defaultFlags = MkTypeFlags False False

public export
record HoleFlags where
  constructor MkHoleFlags
  implbind : Bool -- stands for an implicitly bound name
  precisetype : Bool -- don't generalise multiplicities when instantiating

export
holeInit : Bool -> HoleFlags
holeInit b = MkHoleFlags b False

public export
data Def : Type where
    None : Def -- Not yet defined
    PMDef : (pminfo : PMDefInfo) ->
            (args : List Name) ->
            (treeCT : CaseTree args) ->
            (treeRT : CaseTree args) ->
            (pats : List (vs ** (Env Term vs, Term vs, Term vs))) ->
                -- original checked patterns (LHS/RHS) with the names in
                -- the environment. Used for display purposes, for helping
                -- find size changes in termination checking, and for
                -- generating specialised definitions (so needs to be the
                -- full, non-erased, term)
            Def -- Ordinary function definition
    ExternDef : (arity : Nat) -> Def
    ForeignDef : (arity : Nat) ->
                 List String -> -- supported calling conventions,
                                -- e.g "C:printf,libc,stdlib.h", "scheme:display", ...
                 Def
    Builtin : {arity : Nat} -> PrimFn arity -> Def
    DCon : (tag : Int) -> (arity : Nat) ->
           (newtypeArg : Maybe (Bool, Nat)) ->
               -- if only constructor, and only one argument is non-Rig0,
               -- flag it here. The Nat is the unerased argument position.
               -- The Bool is 'True' if there is no %World token in the
               -- structure, which means it is safe to completely erase
               -- when pattern matching (otherwise we still have to ensure
               -- that the value is inspected, to make sure external effects
               -- happen)
           Def -- data constructor
    TCon : (tag : Int) -> (arity : Nat) ->
           (parampos : List Nat) -> -- parameters
           (detpos : List Nat) -> -- determining arguments
           (flags : TypeFlags) -> -- should 'auto' implicits check
           (mutwith : List Name) ->
           (datacons : List Name) ->
           (detagabbleBy : Maybe (List Nat)) ->
                    -- argument positions which can be used for
                    -- detagging, if it's possible (to check if it's
                    -- safe to erase)
           Def
    Hole : (numlocs : Nat) -> -- Number of locals in scope at binding point
                              -- (mostly to help display)
           HoleFlags ->
           Def
    BySearch : RigCount -> (maxdepth : Nat) -> (defining : Name) -> Def
    -- Constraints are integer references into the current map of
    -- constraints in the UnifyState (see Core.UnifyState)
    Guess : (guess : ClosedTerm) ->
            (envbind : Nat) -> -- Number of things in the environment when
                               -- we guessed the term
            (constraints : List Int) -> Def
    ImpBind : Def -- global name temporarily standing for an implicitly bound name
    -- a name standing for a universe level in a Type
    UniverseLevel : Integer -> Def
    -- A delayed elaboration. The elaborators themselves are stored in the
    -- unification state
    Delayed : Def

export
defNameType : Def -> Maybe NameType
defNameType None = Nothing
defNameType (PMDef {}) = Just Func
defNameType (ExternDef {}) = Just Func
defNameType (ForeignDef {}) = Just Func
defNameType (Builtin {}) = Just Func
defNameType (DCon tag ar _) = Just (DataCon tag ar)
defNameType (TCon tag ar _ _ _ _ _ _) = Just (TyCon tag ar)
defNameType (Hole {}) = Just Func
defNameType (BySearch {}) = Nothing
defNameType (Guess {}) = Nothing
defNameType ImpBind = Just Bound
defNameType (UniverseLevel {}) = Nothing
defNameType Delayed = Nothing

export
covering
Show Def where
  show None = "undefined"
  show (PMDef _ args ct rt pats)
      = unlines [ show args ++ ";"
                , "Compile time tree: " ++ show ct
                , "Run time tree: " ++ show rt
                ]
  show (DCon t a nt)
      = "DataCon " ++ show t ++ " " ++ show a
           ++ maybe "" (\n => " (newtype by " ++ show n ++ ")") nt
  show (TCon t a ps ds u ms cons det)
      = "TyCon " ++ show t ++ " " ++ show a ++ " params: " ++ show ps ++
        " constructors: " ++ show cons ++
        " mutual with: " ++ show ms ++
        " detaggable by: " ++ show det
  show (ExternDef arity) = "<external def with arity " ++ show arity ++ ">"
  show (ForeignDef a cs) = "<foreign def with arity " ++ show a ++
                           " " ++ show cs ++">"
  show (Builtin {arity} _) = "<builtin with arith " ++ show arity ++ ">"
  show (Hole _ p) = "Hole" ++ if implbind p then " [impl]" else ""
  show (BySearch c depth def) = "Search in " ++ show def
  show (Guess tm _ cs) = "Guess " ++ show tm ++ " when " ++ show cs
  show (UniverseLevel i) = "Universe level #" ++ show i
  show ImpBind = "Bound name"
  show Delayed = "Delayed"

public export
record Constructor where
  constructor MkCon
  loc : FC
  name : Name
  arity : Nat
  type : ClosedTerm
%name Constructor cons

public export
data DataDef : Type where
     MkData : (tycon : Constructor) -> (datacons : List Constructor) ->
              DataDef

public export
data Clause : Type where
     MkClause : {vars : _} ->
                (env : Env Term vars) ->
                (lhs : Term vars) -> (rhs : Term vars) -> Clause
%name Clause cl

export
covering
Show Clause where
  show (MkClause {vars} env lhs rhs)
      = show vars ++ ": " ++ show lhs ++ " = " ++ show rhs

public export
data DefFlag
    = Inline
    | NoInline
    | ||| A definition has been marked as deprecated
      Deprecate
    | Invertible -- assume safe to cancel arguments in unification
    | Overloadable -- allow ad-hoc overloads
    | TCInline -- always inline before totality checking
         -- (in practice, this means it's reduced in 'normaliseHoles')
         -- This means the function gets inlined when calculating the size
         -- change graph, but otherwise not. It's only safe if the function
         -- being inlined is terminating no matter what, and is really a bit
         -- of a hack to make sure interface dictionaries are properly inlined
         -- (otherwise they look potentially non terminating) so use with
         -- care!
    | SetTotal TotalReq
    | BlockedHint -- a hint, but blocked for the moment (so don't use)
    | Macro
    | PartialEval (List (Name, Nat)) -- Partially evaluate on completing defintion.
         -- This means the definition is standing for a specialisation so we
         -- should evaluate the RHS, with reduction limits on the given names,
         -- and ensure the name has made progress in doing so (i.e. has reduced
         -- at least once)
    | AllGuarded -- safe to treat as a constructor for the purposes of
         -- productivity checking. All clauses are guarded by constructors,
         -- and there are no other function applications
    | ConType ConInfo
         -- Is it a special type of constructor, e.g. a nil or cons shaped
         -- thing, that can be compiled specially?
    | Identity Nat
         -- Is it the identity function at runtime?
         -- The nat represents which argument the function evaluates to
%name DefFlag dflag

export
Eq DefFlag where
    (==) Inline Inline = True
    (==) NoInline NoInline = True
    (==) Deprecate Deprecate = True
    (==) Invertible Invertible = True
    (==) Overloadable Overloadable = True
    (==) TCInline TCInline = True
    (==) (SetTotal x) (SetTotal y) = x == y
    (==) BlockedHint BlockedHint = True
    (==) Macro Macro = True
    (==) (PartialEval x) (PartialEval y) = x == y
    (==) AllGuarded AllGuarded = True
    (==) (ConType x) (ConType y) = x == y
    (==) (Identity x) (Identity y) = x == y
    (==) _ _ = False

export
Show DefFlag where
  show Inline = "inline"
  show NoInline = "noinline"
  show Deprecate = "deprecate"
  show Invertible = "invertible"
  show Overloadable = "overloadable"
  show TCInline = "tcinline"
  show (SetTotal x) = show x
  show BlockedHint = "blockedhint"
  show Macro = "macro"
  show (PartialEval _) = "partialeval"
  show AllGuarded = "allguarded"
  show (ConType ci) = "contype " ++ show ci
  show (Identity x) = "identity " ++ show x

public export
data SizeChange = Smaller | Same | Unknown

export
Show SizeChange where
  show Smaller = "Smaller"
  show Same = "Same"
  show Unknown = "Unknown"

export
Eq SizeChange where
  Smaller == Smaller = True
  Same == Same = True
  Unknown == Unknown = True
  _ == _ = False

public export
record SCCall where
     constructor MkSCCall
     fnCall : Name -- Function called
     fnArgs : List (Maybe (Nat, SizeChange))
        -- relationship to arguments of calling function; argument position
        -- (in the calling function), and how its size changed in the call.
        -- 'Nothing' if it's not related to any of the calling function's
        -- arguments

export
Show SCCall where
  show c = show (fnCall c) ++ ": " ++ show (fnArgs c)

export
Eq SCCall where
  x == y = fnCall x == fnCall y && fnArgs x == fnArgs y

public export
data SchemeMode
        = EvalAll -- evaluate everything
        | BlockExport -- compile 'export' names in other modules as blocked

export
Eq SchemeMode where
   EvalAll == EvalAll = True
   BlockExport == BlockExport = True
   _ == _ = False

public export
record GlobalDef where
  constructor MkGlobalDef
  location : FC
  fullname : Name -- original unresolved name
  type : ClosedTerm
  eraseArgs : List Nat -- which argument positions to erase at runtime
  safeErase : List Nat -- which argument positions are safe to assume
                       -- erasable without 'dotting', because their types
                       -- are collapsible relative to non-erased arguments
  specArgs : List Nat -- arguments to specialise by
  inferrable : List Nat -- arguments which can be inferred from elsewhere in the type
  multiplicity : RigCount
  localVars : List Name -- environment name is defined in
  visibility : Visibility
  totality : Totality
  flags : List DefFlag
  refersToM : Maybe (NameMap Bool)
  refersToRuntimeM : Maybe (NameMap Bool)
  invertible : Bool -- for an ordinary definition, is it invertible in unification
  noCycles : Bool -- for metavariables, whether they can be cyclic (this
                  -- would only be allowed when using a metavariable as a
                  -- placeholder for a yet to be elaborated arguments, but
                  -- not for implicits because that'd indicate failing the
                  -- occurs check)
  linearChecked : Bool -- Flag whether we've already checked its linearity
  definition : Def
  compexpr : Maybe CDef
  namedcompexpr : Maybe NamedDef
  sizeChange : List SCCall
  schemeExpr : Maybe (SchemeMode, SchemeObj Write)

export
gDefKindedName : GlobalDef -> KindedName
gDefKindedName def
  = let nm = fullname def in
    MkKindedName (defNameType $ definition def) nm nm

export
refersTo : GlobalDef -> NameMap Bool
refersTo def = maybe empty id (refersToM def)

export
refersToRuntime : GlobalDef -> NameMap Bool
refersToRuntime def = maybe empty id (refersToRuntimeM def)

export
findSetTotal : List DefFlag -> Maybe TotalReq
findSetTotal [] = Nothing
findSetTotal (SetTotal t :: _) = Just t
findSetTotal (_ :: xs) = findSetTotal xs

-- Label for array references
export
data Arr : Type where

-- A context entry. If it's never been looked up, we haven't decoded the
-- binary blob yet, so decode it first time
public export
data ContextEntry : Type where
     Coded : Namespace -> -- namespace for decoding into, with restoreNS
             Binary -> ContextEntry
     Decoded : GlobalDef -> ContextEntry

public export
data PossibleName : Type where
     Direct : Name -> Int -> PossibleName -- full name and resolved name id
     Alias : Name -> -- aliased name (from "import as")
             Name -> Int -> -- real full name and resolved name, as above
             PossibleName

public export
data UConstraint : Type where
     ULE : Name -> Name -> UConstraint
     ULT : Name -> Name -> UConstraint

export
Eq UConstraint where
  ULE x y == ULE x' y' = x == x' && y == y'
  ULT x y == ULT x' y' = x == x' && y == y'
  _ == _ = False

export
Ord UConstraint where
  compare (ULE _ _) (ULT _ _) = LT
  compare (ULT _ _) (ULE _ _) = GT
  compare (ULE x y) (ULE x' y')
      = case compare x x' of
             EQ => compare y y'
             t => t
  compare (ULT x y) (ULT x' y')
      = case compare x x' of
             EQ => compare y y'
             t => t

-- All the GlobalDefs. We can only have one context, because name references
-- point at locations in here, and if we have more than one the indices won't
-- match up. So, this isn't polymorphic.
public export
record Context where
    constructor MkContext
    firstEntry : Int -- First entry in the current source file
    nextEntry : Int
    -- Map from full name to its position in the context
    resolvedAs : NameMap Int
    -- Map from usernames to all the possible names in all namespaces
    possibles : UserNameMap (List PossibleName)
    -- Reference to the actual content, indexed by Int
    content : Ref Arr (IOArray ContextEntry)
    -- Branching depth, in a backtracking elaborator. 0 is top level; at lower
    -- levels we need to stage updates rather than add directly to the
    -- 'content' store
    branchDepth : Nat
    -- Things which we're going to add, if this branch succeeds
    staging : IntMap ContextEntry

    -- Namespaces which are visible (i.e. have been imported)
    -- This only matters during evaluation and type checking, to control
    -- access in a program - in all other cases, we'll assume everything is
    -- visible
    visibleNS : List Namespace
    allPublic : Bool -- treat everything as public. This is intended
                     -- for checking partially evaluated definitions
                     -- or for use outside of the main compilation
                     -- process (e.g. when implementing interactive
                     -- features such as case splitting).
    inlineOnly : Bool -- only return things with the 'alwaysReduce' flag
    hidden : NameMap () -- Never return these
    uconstraints : List UConstraint

%name Context gam

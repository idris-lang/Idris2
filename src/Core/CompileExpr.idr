-- Representation of expressions ready for compiling
-- Type erased, explicit case trees
module Core.CompileExpr

import Core.FC
import Core.Name
import Core.TT

import Data.List
import Data.NameMap
import Data.Vect

%default covering

mutual
  ||| CExp - an expression ready for compiling.
  public export
  data CExp : List Name -> Type where
       CLocal : {idx : Nat} -> FC -> (0 p : IsVar x idx vars) -> CExp vars
       CRef : FC -> Name -> CExp vars
       -- Lambda expression
       CLam : FC -> (x : Name) -> CExp (x :: vars) -> CExp vars
       -- Let bindings
       CLet : FC -> (x : Name) -> (inlineOK : Bool) -> -- Don't inline if set
              CExp vars -> CExp (x :: vars) -> CExp vars
       -- Application of a defined function. The length of the argument list is
       -- exactly the same length as expected by its definition (so saturate with
       -- lambdas if necessary, or overapply with additional CApps)
       CApp : FC -> CExp vars -> List (CExp vars) -> CExp vars
       -- A saturated constructor application
       CCon : FC -> Name -> (tag : Maybe Int) -> List (CExp vars) -> CExp vars
       -- Internally defined primitive operations
       COp : {arity : _} ->
             FC -> PrimFn arity -> Vect arity (CExp vars) -> CExp vars
       -- Externally defined primitive operations
       CExtPrim : FC -> (p : Name) -> List (CExp vars) -> CExp vars
       -- A forced (evaluated) value
       CForce : FC -> CExp vars -> CExp vars
       -- A delayed value
       CDelay : FC -> CExp vars -> CExp vars
       -- A case match statement
       CConCase : FC -> (sc : CExp vars) -> List (CConAlt vars) -> Maybe (CExp vars) -> CExp vars
       CConstCase : FC -> (sc : CExp vars) -> List (CConstAlt vars) -> Maybe (CExp vars) -> CExp vars
       -- A primitive value
       CPrimVal : FC -> Constant -> CExp vars
       -- An erased value
       CErased : FC -> CExp vars
       -- Some sort of crash?
       CCrash : FC -> String -> CExp vars

  public export
  data CConAlt : List Name -> Type where
       -- If no tag, then match by constructor name. Back ends might want to
       -- convert names to a unique integer for performance.
       MkConAlt : Name -> (tag : Maybe Int) -> (args : List Name) ->
                  CExp (args ++ vars) -> CConAlt vars

  public export
  data CConstAlt : List Name -> Type where
       MkConstAlt : Constant -> CExp vars -> CConstAlt vars

mutual
  ||| NamedCExp - as above, but without the name index, so with explicit
  ||| names, which are faster (but less safe) to manipulate in the inliner.
  ||| You can, howeveer, assume that name bindings are unique - translation
  ||| to this form (and the liner) ensure that, even if the type doesn't
  ||| guarantee it!
  public export
  data NamedCExp : Type where
       NmLocal : FC -> Name -> NamedCExp
       NmRef : FC -> Name -> NamedCExp
       -- Lambda expression
       NmLam : FC -> (x : Name) -> NamedCExp -> NamedCExp
       -- Let bindings
       NmLet : FC -> (x : Name) -> NamedCExp -> NamedCExp -> NamedCExp
       -- Application of a defined function. The length of the argument list is
       -- exactly the same length as expected by its definition (so saturate with
       -- lambdas if necessary, or overapply with additional CApps)
       NmApp : FC -> NamedCExp -> List NamedCExp -> NamedCExp
       -- A saturated constructor application
       NmCon : FC -> Name -> (tag : Maybe Int) -> List NamedCExp -> NamedCExp
       -- Internally defined primitive operations
       NmOp : FC -> PrimFn arity -> Vect arity NamedCExp -> NamedCExp
       -- Externally defined primitive operations
       NmExtPrim : FC -> (p : Name) -> List NamedCExp -> NamedCExp
       -- A forced (evaluated) value
       NmForce : FC -> NamedCExp -> NamedCExp
       -- A delayed value
       NmDelay : FC -> NamedCExp -> NamedCExp
       -- A case match statement
       NmConCase : FC -> (sc : NamedCExp) -> List NamedConAlt -> Maybe NamedCExp -> NamedCExp
       NmConstCase : FC -> (sc : NamedCExp) -> List NamedConstAlt -> Maybe NamedCExp -> NamedCExp
       -- A primitive value
       NmPrimVal : FC -> Constant -> NamedCExp
       -- An erased value
       NmErased : FC -> NamedCExp
       -- Some sort of crash?
       NmCrash : FC -> String -> NamedCExp

  public export
  data NamedConAlt : Type where
       MkNConAlt : Name -> (tag : Maybe Int) -> (args : List Name) ->
                   NamedCExp -> NamedConAlt

  public export
  data NamedConstAlt : Type where
       MkNConstAlt : Constant -> NamedCExp -> NamedConstAlt

-- Argument type descriptors for foreign function calls
public export
data CFType : Type where
     CFUnit : CFType
     CFInt : CFType
     CFUnsigned : CFType
     CFString : CFType
     CFDouble : CFType
     CFChar : CFType
     CFPtr : CFType
     CFGCPtr : CFType
     CFBuffer : CFType
     CFWorld : CFType
     CFFun : CFType -> CFType -> CFType
     CFIORes : CFType -> CFType
     CFStruct : String -> List (String, CFType) -> CFType
     CFUser : Name -> List CFType -> CFType

public export
data CDef : Type where
     -- Normal function definition
     MkFun : (args : List Name) -> CExp args -> CDef
     -- Constructor
     MkCon : (tag : Maybe Int) -> (arity : Nat) -> (nt : Maybe Nat) -> CDef
     -- Foreign definition
     MkForeign : (ccs : List String) ->
                 (fargs : List CFType) ->
                 CFType ->
                 CDef
     -- A function which will fail at runtime (usually due to being a hole) so needs
     -- to run, discarding arguments, no matter how many arguments are passed
     MkError : CExp [] -> CDef

public export
data NamedDef : Type where
     -- Normal function definition
     MkNmFun : (args : List Name) -> NamedCExp -> NamedDef
     -- Constructor
     MkNmCon : (tag : Maybe Int) -> (arity : Nat) -> (nt : Maybe Nat) -> NamedDef
     -- Foreign definition
     MkNmForeign : (ccs : List String) ->
                   (fargs : List CFType) ->
                   CFType ->
                   NamedDef
     -- A function which will fail at runtime (usually due to being a hole) so needs
     -- to run, discarding arguments, no matter how many arguments are passed
     MkNmError : NamedCExp -> NamedDef

mutual
  export
  Show NamedCExp where
    show (NmLocal _ x) = "!" ++ show x
    show (NmRef _ x) = show x
    show (NmLam _ x y) = "(%lam " ++ show x ++ " " ++ show y ++ ")"
    show (NmLet _ x y z) = "(%let " ++ show x ++ " " ++ show y ++ " " ++ show z ++ ")"
    show (NmApp _ x xs)
        = assert_total $ "(" ++ show x ++ " " ++ show xs ++ ")"
    show (NmCon _ x tag xs)
        = assert_total $ "(%con " ++ show x ++ " " ++ show tag ++ " " ++ show xs ++ ")"
    show (NmOp _ op xs)
        = assert_total $ "(" ++ show op ++ " " ++ show xs ++ ")"
    show (NmExtPrim _ p xs)
        = assert_total $ "(%extern " ++ show p ++ " " ++ show xs ++ ")"
    show (NmForce _ x) = "(%force " ++ show x ++ ")"
    show (NmDelay _ x) = "(%delay " ++ show x ++ ")"
    show (NmConCase _ sc xs def)
        = assert_total $ "(%case " ++ show sc ++ " " ++ show xs ++ " " ++ show def ++ ")"
    show (NmConstCase _ sc xs def)
        = assert_total $ "(%case " ++ show sc ++ " " ++ show xs ++ " " ++ show def ++ ")"
    show (NmPrimVal _ x) = show x
    show (NmErased _) = "___"
    show (NmCrash _ x) = "(CRASH " ++ show x ++ ")"

  export
  Show NamedConAlt where
    show (MkNConAlt x tag args exp)
         = "(%concase " ++ show x ++ " " ++ show tag ++ " " ++
             show args ++ " " ++ show exp ++ ")"

  export
  Show NamedConstAlt where
    show (MkNConstAlt x exp)
         = "(%constcase " ++ show x ++ " " ++ show exp ++ ")"

export
data Names : List Name -> Type where
     Nil : Names []
     (::) : Name -> Names xs -> Names (x :: xs)

elem : Name -> Names xs -> Bool
elem n [] = False
elem n (x :: xs) = n == x || elem n xs

tryNext : Name -> Name
tryNext (UN n) = MN n 0
tryNext (MN n i) = MN n (1 + i)
tryNext n = MN (nameRoot n) 0

uniqueName : Name -> Names vs -> Name
uniqueName s ns =
    if s `elem` ns
       then uniqueName (tryNext s) ns
       else s

export
getLocName : (idx : Nat) -> Names vars -> (0 p : IsVar name idx vars) -> Name
getLocName Z (x :: xs) First = x
getLocName (S k) (x :: xs) (Later p) = getLocName k xs p

export
addLocs : (args : List Name) -> Names vars -> Names (args ++ vars)
addLocs [] ns = ns
addLocs (x :: xs) ns
    = let rec = addLocs xs ns in
          uniqueName x rec :: rec

conArgs : (args : List Name) -> Names (args ++ vars) -> List Name
conArgs [] ns = []
conArgs (a :: as) (n :: ns) = n :: conArgs as ns

mutual
  forgetExp : Names vars -> CExp vars -> NamedCExp
  forgetExp locs (CLocal fc p) = NmLocal fc (getLocName _ locs p)
  forgetExp locs (CRef fc n) = NmRef fc n
  forgetExp locs (CLam fc x sc)
      = let locs' = addLocs [x] locs in
            NmLam fc (getLocName _ locs' First) (forgetExp locs' sc)
  forgetExp locs (CLet fc x _ val sc)
      = let locs' = addLocs [x] locs in
            NmLet fc (getLocName _ locs' First)
                     (forgetExp locs val)
                     (forgetExp locs' sc)
  forgetExp locs (CApp fc f args)
      = NmApp fc (forgetExp locs f) (map (forgetExp locs) args)
  forgetExp locs (CCon fc n t args)
      = NmCon fc n t (map (forgetExp locs) args)
  forgetExp locs (COp fc op args)
      = NmOp fc op (map (forgetExp locs) args)
  forgetExp locs (CExtPrim fc p args)
      = NmExtPrim fc p (map (forgetExp locs) args)
  forgetExp locs (CForce fc f)
      = NmForce fc (forgetExp locs f)
  forgetExp locs (CDelay fc f)
      = NmDelay fc (forgetExp locs f)
  forgetExp locs (CConCase fc sc alts def)
      = NmConCase fc (forgetExp locs sc) (map (forgetConAlt locs) alts)
                     (map (forgetExp locs) def)
  forgetExp locs (CConstCase fc sc alts def)
      = NmConstCase fc (forgetExp locs sc) (map (forgetConstAlt locs) alts)
                       (map (forgetExp locs) def)
  forgetExp locs (CPrimVal fc c) = NmPrimVal fc c
  forgetExp locs (CErased fc) = NmErased fc
  forgetExp locs (CCrash fc msg) = NmCrash fc msg

  forgetConAlt : Names vars -> CConAlt vars -> NamedConAlt
  forgetConAlt locs (MkConAlt n t args exp)
      = let args' = addLocs args locs in
            MkNConAlt n t (conArgs args args') (forgetExp args' exp)

  forgetConstAlt : Names vars -> CConstAlt vars -> NamedConstAlt
  forgetConstAlt locs (MkConstAlt c exp)
      = MkNConstAlt c (forgetExp locs exp)

export
forget : {vars : _} -> CExp vars -> NamedCExp
forget {vars} exp
    = forgetExp (addLocs vars [])
                (rewrite appendNilRightNeutral vars in exp)

export
forgetDef : CDef -> NamedDef
forgetDef (MkFun args def)
    = let ns = addLocs args []
          args' = conArgs {vars = []} args ns in
          MkNmFun args' (forget def)
forgetDef (MkCon t a nt) = MkNmCon t a nt
forgetDef (MkForeign ccs fargs ty) = MkNmForeign ccs fargs ty
forgetDef (MkError err) = MkNmError (forget err)

export
{vars : _} -> Show (CExp vars) where
  show exp = show (forget exp)

export
Show CFType where
  show CFUnit = "Unit"
  show CFInt = "Int"
  show CFUnsigned = "Bits_n"
  show CFString = "String"
  show CFDouble = "Double"
  show CFChar = "Char"
  show CFPtr = "Ptr"
  show CFGCPtr = "GCPtr"
  show CFBuffer = "Buffer"
  show CFWorld = "%World"
  show (CFFun s t) = show s ++ " -> " ++ show t
  show (CFIORes t) = "IORes " ++ show t
  show (CFStruct n args) = "struct " ++ show n ++ " " ++ showSep " " (map show args)
  show (CFUser n args) = show n ++ " " ++ showSep " " (map show args)

export
Show CDef where
  show (MkFun args exp) = show args ++ ": " ++ show exp
  show (MkCon tag arity pos)
      = "Constructor tag " ++ show tag ++ " arity " ++ show arity ++
        maybe "" (\n => " (newtype by " ++ show n ++ ")") pos
  show (MkForeign ccs args ret)
      = "Foreign call " ++ show ccs ++ " " ++
        show args ++ " -> " ++ show ret
  show (MkError exp) = "Error: " ++ show exp

export
Show NamedDef where
  show (MkNmFun args exp) = show args ++ ": " ++ show exp
  show (MkNmCon tag arity pos)
      = "Constructor tag " ++ show tag ++ " arity " ++ show arity ++
        maybe "" (\n => " (newtype by " ++ show n ++ ")") pos
  show (MkNmForeign ccs args ret)
      = "Foreign call " ++ show ccs ++ " " ++
        show args ++ " -> " ++ show ret
  show (MkNmError exp) = "Error: " ++ show exp

mutual
  export
  insertNames : {outer, inner : _} ->
                (ns : List Name) -> CExp (outer ++ inner) ->
                CExp (outer ++ (ns ++ inner))
  insertNames ns (CLocal fc prf)
      = let MkNVar var' = insertNVarNames {ns} _ prf in
            CLocal fc var'
  insertNames _ (CRef fc x) = CRef fc x
  insertNames {outer} {inner} ns (CLam fc x sc)
      = let sc' = insertNames {outer = x :: outer} {inner} ns sc in
            CLam fc x sc'
  insertNames {outer} {inner} ns (CLet fc x inl val sc)
      = let sc' = insertNames {outer = x :: outer} {inner} ns sc in
            CLet fc x inl (insertNames ns val) sc'
  insertNames ns (CApp fc x xs)
      = CApp fc (insertNames ns x) (assert_total (map (insertNames ns) xs))
  insertNames ns (CCon fc x tag xs)
      = CCon fc x tag (assert_total (map (insertNames ns) xs))
  insertNames ns (COp fc x xs)
      = COp fc x (assert_total (map (insertNames ns) xs))
  insertNames ns (CExtPrim fc p xs)
      = CExtPrim fc p (assert_total (map (insertNames ns) xs))
  insertNames ns (CForce fc x) = CForce fc (insertNames ns x)
  insertNames ns (CDelay fc x) = CDelay fc (insertNames ns x)
  insertNames ns (CConCase fc sc xs def)
      = CConCase fc (insertNames ns sc) (assert_total (map (insertNamesConAlt ns) xs))
                 (assert_total (map (insertNames ns) def))
  insertNames ns (CConstCase fc sc xs def)
      = CConstCase fc (insertNames ns sc) (assert_total (map (insertNamesConstAlt ns) xs))
                   (assert_total (map (insertNames ns) def))
  insertNames _ (CPrimVal fc x) = CPrimVal fc x
  insertNames _ (CErased fc) = CErased fc
  insertNames _ (CCrash fc x) = CCrash fc x

  insertNamesConAlt : {outer, inner : _} ->
                      (ns : List Name) -> CConAlt (outer ++ inner) -> CConAlt (outer ++ (ns ++ inner))
  insertNamesConAlt {outer} {inner} ns (MkConAlt x tag args sc)
        = let sc' : CExp ((args ++ outer) ++ inner)
                  = rewrite sym (appendAssociative args outer inner) in sc in
              MkConAlt x tag args
               (rewrite appendAssociative args outer (ns ++ inner) in
                        insertNames ns sc')

  insertNamesConstAlt : {outer, inner : _} ->
                        (ns : List Name) -> CConstAlt (outer ++ inner) -> CConstAlt (outer ++ (ns ++ inner))
  insertNamesConstAlt ns (MkConstAlt x sc) = MkConstAlt x (insertNames ns sc)

mutual
  export
  embed : CExp args -> CExp (args ++ vars)
  embed cexp = believe_me cexp
  -- It is identity at run time, but it would be implemented as below
  -- (not sure theere's much performance benefit, mind...)
  {-
  embed (CLocal fc prf) = CLocal fc (varExtend prf)
  embed (CRef fc n) = CRef fc n
  embed (CLam fc x sc) = CLam fc x (embed sc)
  embed (CLet fc x inl val sc) = CLet fc x inl (embed val) (embed sc)
  embed (CApp fc f args) = CApp fc (embed f) (assert_total (map embed args))
  embed (CCon fc n t args) = CCon fc n t (assert_total (map embed args))
  embed (COp fc p args) = COp fc p (assert_total (map embed args))
  embed (CExtPrim fc p args) = CExtPrim fc p (assert_total (map embed args))
  embed (CForce fc e) = CForce fc (embed e)
  embed (CDelay fc e) = CDelay fc (embed e)
  embed (CConCase fc sc alts def)
      = CConCase fc (embed sc) (assert_total (map embedAlt alts))
                 (assert_total (map embed def))
  embed (CConstCase fc sc alts def)
      = CConstCase fc (embed sc) (assert_total (map embedConstAlt alts))
                   (assert_total (map embed def))
  embed (CPrimVal fc c) = CPrimVal fc c
  embed (CErased fc) = CErased fc
  embed (CCrash fc msg) = CCrash fc msg

  embedAlt : CConAlt args -> CConAlt (args ++ vars)
  embedAlt {args} {vars} (MkConAlt n t as sc)
     = MkConAlt n t as (rewrite appendAssociative as args vars in embed sc)

  embedConstAlt : CConstAlt args -> CConstAlt (args ++ vars)
  embedConstAlt (MkConstAlt c sc) = MkConstAlt c (embed sc)
  -}

mutual
  -- Shrink the scope of a compiled expression, replacing any variables not
  -- in the remaining set with Erased
  export
  shrinkCExp : SubVars newvars vars -> CExp vars -> CExp newvars
  shrinkCExp sub (CLocal fc prf)
      = case subElem prf sub of
             Nothing => CErased fc
             Just (MkVar prf') => CLocal fc prf'
  shrinkCExp _ (CRef fc x) = CRef fc x
  shrinkCExp sub (CLam fc x sc)
      = let sc' = shrinkCExp (KeepCons sub) sc in
            CLam fc x sc'
  shrinkCExp sub (CLet fc x inl val sc)
      = let sc' = shrinkCExp (KeepCons sub) sc in
            CLet fc x inl (shrinkCExp sub val) sc'
  shrinkCExp sub (CApp fc x xs)
      = CApp fc (shrinkCExp sub x) (assert_total (map (shrinkCExp sub) xs))
  shrinkCExp sub (CCon fc x tag xs)
      = CCon fc x tag (assert_total (map (shrinkCExp sub) xs))
  shrinkCExp sub (COp fc x xs)
      = COp fc x (assert_total (map (shrinkCExp sub) xs))
  shrinkCExp sub (CExtPrim fc p xs)
      = CExtPrim fc p (assert_total (map (shrinkCExp sub) xs))
  shrinkCExp sub (CForce fc x) = CForce fc (shrinkCExp sub x)
  shrinkCExp sub (CDelay fc x) = CDelay fc (shrinkCExp sub x)
  shrinkCExp sub (CConCase fc sc xs def)
      = CConCase fc (shrinkCExp sub sc)
                 (assert_total (map (shrinkConAlt sub) xs))
                 (assert_total (map (shrinkCExp sub) def))
  shrinkCExp sub (CConstCase fc sc xs def)
      = CConstCase fc (shrinkCExp sub sc)
                   (assert_total (map (shrinkConstAlt sub) xs))
                   (assert_total (map (shrinkCExp sub) def))
  shrinkCExp _ (CPrimVal fc x) = CPrimVal fc x
  shrinkCExp _ (CErased fc) = CErased fc
  shrinkCExp _ (CCrash fc x) = CCrash fc x

  shrinkConAlt : SubVars newvars vars -> CConAlt vars -> CConAlt newvars
  shrinkConAlt sub (MkConAlt x tag args sc)
        = MkConAlt x tag args (shrinkCExp (subExtend args sub) sc)

  shrinkConstAlt : SubVars newvars vars -> CConstAlt vars -> CConstAlt newvars
  shrinkConstAlt sub (MkConstAlt x sc) = MkConstAlt x (shrinkCExp sub sc)

export
Weaken CExp where
  weakenNs ns tm = insertNames {outer = []} ns tm

-- Substitute some explicit terms for names in a term, and remove those
-- names from the scope
namespace SubstCEnv
  public export
  data SubstCEnv : List Name -> List Name -> Type where
       Nil : SubstCEnv [] vars
       (::) : CExp vars ->
              SubstCEnv ds vars -> SubstCEnv (d :: ds) vars

findDrop : {drop : _} -> {idx : Nat} ->
           FC -> (0 p : IsVar name idx (drop ++ vars)) ->
           SubstCEnv drop vars -> CExp vars
findDrop {drop = []} fc var env = CLocal fc var
findDrop {drop = x :: xs} fc First (tm :: env) = tm
findDrop {drop = x :: xs} fc (Later p) (tm :: env) = findDrop fc p env

find : {outer, drop, vars : _} -> {idx : Nat} ->
       FC -> (0 p : IsVar name idx (outer ++ (drop ++ vars))) ->
       SubstCEnv drop vars ->
       CExp (outer ++ vars)
find {outer = []} fc var env = findDrop fc var env
find {outer = x :: xs} fc First env = CLocal fc First
find {outer = x :: xs} fc (Later p) env = weaken (find fc p env)

mutual
  substEnv : {outer, drop, vars : _} ->
             SubstCEnv drop vars -> CExp (outer ++ (drop ++ vars)) ->
             CExp (outer ++ vars)
  substEnv env (CLocal fc prf)
      = find fc prf env
  substEnv _ (CRef fc x) = CRef fc x
  substEnv {outer} env (CLam fc x sc)
      = let sc' = substEnv {outer = x :: outer} env sc in
            CLam fc x sc'
  substEnv {outer} env (CLet fc x inl val sc)
      = let sc' = substEnv {outer = x :: outer} env sc in
            CLet fc x inl (substEnv env val) sc'
  substEnv env (CApp fc x xs)
      = CApp fc (substEnv env x) (assert_total (map (substEnv env) xs))
  substEnv env (CCon fc x tag xs)
      = CCon fc x tag (assert_total (map (substEnv env) xs))
  substEnv env (COp fc x xs)
      = COp fc x (assert_total (map (substEnv env) xs))
  substEnv env (CExtPrim fc p xs)
      = CExtPrim fc p (assert_total (map (substEnv env) xs))
  substEnv env (CForce fc x) = CForce fc (substEnv env x)
  substEnv env (CDelay fc x) = CDelay fc (substEnv env x)
  substEnv env (CConCase fc sc xs def)
      = CConCase fc (substEnv env sc)
                 (assert_total (map (substConAlt env) xs))
                 (assert_total (map (substEnv env) def))
  substEnv env (CConstCase fc sc xs def)
      = CConstCase fc (substEnv env sc)
                   (assert_total (map (substConstAlt env) xs))
                   (assert_total (map (substEnv env) def))
  substEnv _ (CPrimVal fc x) = CPrimVal fc x
  substEnv _ (CErased fc) = CErased fc
  substEnv _ (CCrash fc x) = CCrash fc x

  substConAlt : {outer, drop, vars : _} ->
                SubstCEnv drop vars -> CConAlt (outer ++ (drop ++ vars)) ->
                CConAlt (outer ++ vars)
  substConAlt {vars} {outer} {drop} env (MkConAlt x tag args sc)
      = MkConAlt x tag args
           (rewrite appendAssociative args outer vars in
                    substEnv {outer = args ++ outer} env
                      (rewrite sym (appendAssociative args outer (drop ++ vars)) in
                               sc))

  substConstAlt : {outer, drop, vars : _} ->
                  SubstCEnv drop vars -> CConstAlt (outer ++ (drop ++ vars)) ->
                  CConstAlt (outer ++ vars)
  substConstAlt env (MkConstAlt x sc) = MkConstAlt x (substEnv env sc)

export
substs : {drop, vars : _} ->
         SubstCEnv drop vars -> CExp (drop ++ vars) -> CExp vars
substs env tm = substEnv {outer = []} env tm

resolveRef : {later : _} ->
             (done : List Name) -> Bounds bound -> FC -> Name ->
             Maybe (CExp (later ++ (done ++ bound ++ vars)))
resolveRef done None fc n = Nothing
resolveRef {later} {vars} done (Add {xs} new old bs) fc n
    = if n == old
         then rewrite appendAssociative later done (new :: xs ++ vars) in
              let MkNVar p = weakenNVar {inner = new :: xs ++ vars}
                                        (later ++ done) First in
                    Just (CLocal fc p)
         else rewrite appendAssociative done [new] (xs ++ vars)
                in resolveRef (done ++ [new]) bs fc n

mutual
  export
  mkLocals : {later, bound, vars : _} ->
             Bounds bound ->
             CExp (later ++ vars) -> CExp (later ++ (bound ++ vars))
  mkLocals bs (CLocal {idx} {x} fc p)
      = let MkNVar p' = addVars bs p in CLocal {x} fc p'
  mkLocals {later} {vars} bs (CRef fc var)
      = maybe (CRef fc var) id (resolveRef [] bs fc var)
  mkLocals {later} {vars} bs (CLam fc x sc)
      = let sc' = mkLocals bs {later = x :: later} {vars} sc in
            CLam fc x sc'
  mkLocals {later} {vars} bs (CLet fc x inl val sc)
      = let sc' = mkLocals bs {later = x :: later} {vars} sc in
            CLet fc x inl (mkLocals bs val) sc'
  mkLocals bs (CApp fc f xs)
      = CApp fc (mkLocals bs f) (assert_total (map (mkLocals bs) xs))
  mkLocals bs (CCon fc x tag xs)
      = CCon fc x tag (assert_total (map (mkLocals bs) xs))
  mkLocals bs (COp fc x xs)
      = COp fc x (assert_total (map (mkLocals bs) xs))
  mkLocals bs (CExtPrim fc x xs)
      = CExtPrim fc x (assert_total (map (mkLocals bs) xs))
  mkLocals bs (CForce fc x)
      = CForce fc (mkLocals bs x)
  mkLocals bs (CDelay fc x)
      = CDelay fc (mkLocals bs x)
  mkLocals bs (CConCase fc sc xs def)
      = CConCase fc (mkLocals bs sc)
                 (assert_total (map (mkLocalsConAlt bs) xs))
                 (assert_total (map (mkLocals bs) def))
  mkLocals bs (CConstCase fc sc xs def)
      = CConstCase fc (mkLocals bs sc)
                 (assert_total (map (mkLocalsConstAlt bs) xs))
                 (assert_total (map (mkLocals bs) def))
  mkLocals bs (CPrimVal fc x) = CPrimVal fc x
  mkLocals bs (CErased fc) = CErased fc
  mkLocals bs (CCrash fc x) = CCrash fc x

  mkLocalsConAlt : {later, bound, vars : _} ->
                   Bounds bound ->
                   CConAlt (later ++ vars) -> CConAlt (later ++ (bound ++ vars))
  mkLocalsConAlt {bound} {later} {vars} bs (MkConAlt x tag args sc)
        = let sc' : CExp ((args ++ later) ++ vars)
                  = rewrite sym (appendAssociative args later vars) in sc in
              MkConAlt x tag args
               (rewrite appendAssociative args later (bound ++ vars) in
                        mkLocals bs sc')

  mkLocalsConstAlt : {later, bound, vars : _} ->
                     Bounds bound ->
                     CConstAlt (later ++ vars) -> CConstAlt (later ++ (bound ++ vars))
  mkLocalsConstAlt bs (MkConstAlt x sc) = MkConstAlt x (mkLocals bs sc)

export
refsToLocals : {bound, vars : _} ->
               Bounds bound -> CExp vars -> CExp (bound ++ vars)
refsToLocals None tm = tm
refsToLocals bs y = mkLocals {later = []} bs y

export
getFC : CExp args -> FC
getFC (CLocal fc _) = fc
getFC (CRef fc _) = fc
getFC (CLam fc _ _) = fc
getFC (CLet fc _ _ _ _) = fc
getFC (CApp fc _ _) = fc
getFC (CCon fc _ _ _) = fc
getFC (COp fc _ _) = fc
getFC (CExtPrim fc _ _) = fc
getFC (CForce fc _) = fc
getFC (CDelay fc _) = fc
getFC (CConCase fc _ _ _) = fc
getFC (CConstCase fc _ _ _) = fc
getFC (CPrimVal fc _) = fc
getFC (CErased fc) = fc
getFC (CCrash fc _) = fc

namespace NamedCExp
  export
  getFC : NamedCExp -> FC
  getFC (NmLocal fc _) = fc
  getFC (NmRef fc _) = fc
  getFC (NmLam fc _ _) = fc
  getFC (NmLet fc _ _ _) = fc
  getFC (NmApp fc _ _) = fc
  getFC (NmCon fc _ _ _) = fc
  getFC (NmOp fc _ _) = fc
  getFC (NmExtPrim fc _ _) = fc
  getFC (NmForce fc _) = fc
  getFC (NmDelay fc _) = fc
  getFC (NmConCase fc _ _ _) = fc
  getFC (NmConstCase fc _ _ _) = fc
  getFC (NmPrimVal fc _) = fc
  getFC (NmErased fc) = fc
  getFC (NmCrash fc _) = fc

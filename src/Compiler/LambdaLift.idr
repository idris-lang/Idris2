module Compiler.LambdaLift

import Core.CompileExpr
import Core.Context
import Core.Core
import Core.TT

import Data.List
import Data.Vect

%default covering

mutual
  public export
  data Lifted : List Name -> Type where
       LLocal : {idx : Nat} -> FC -> (0 p : IsVar x idx vars) -> Lifted vars
       -- A known function applied to exactly the right number of arguments,
       -- so the runtime can Just Go
       LAppName : FC -> Name -> List (Lifted vars) -> Lifted vars
       -- A known function applied to too few arguments, so the runtime should
       -- make a closure and wait for the remaining arguments
       LUnderApp : FC -> Name -> (missing : Nat) ->
                   (args : List (Lifted vars)) -> Lifted vars
       -- A closure applied to one more argument (so, for example a closure
       -- which is waiting for another argument before it can run).
       -- The runtime should add the argument to the closure and run the result
       -- if it is now fully applied.
       LApp : FC -> (closure : Lifted vars) -> (arg : Lifted vars) -> Lifted vars
       LLet : FC -> (x : Name) -> Lifted vars ->
              Lifted (x :: vars) -> Lifted vars
       LCon : FC -> Name -> (tag : Maybe Int) -> List (Lifted vars) -> Lifted vars
       LOp : {arity : _} ->
             FC -> PrimFn arity -> Vect arity (Lifted vars) -> Lifted vars
       LExtPrim : FC -> (p : Name) -> List (Lifted vars) -> Lifted vars
       LConCase : FC -> Lifted vars ->
                  List (LiftedConAlt vars) ->
                  Maybe (Lifted vars) -> Lifted vars
       LConstCase : FC -> Lifted vars ->
                    List (LiftedConstAlt vars) ->
                    Maybe (Lifted vars) -> Lifted vars
       LPrimVal : FC -> Constant -> Lifted vars
       LErased : FC -> Lifted vars
       LCrash : FC -> String -> Lifted vars

  public export
  data LiftedConAlt : List Name -> Type where
       MkLConAlt : Name -> (tag : Maybe Int) -> (args : List Name) ->
                   Lifted (args ++ vars) -> LiftedConAlt vars

  public export
  data LiftedConstAlt : List Name -> Type where
       MkLConstAlt : Constant -> Lifted vars -> LiftedConstAlt vars

public export
data LiftedDef : Type where
     -- We take the outer scope and the function arguments separately so that
     -- we don't have to reshuffle de Bruijn indices, which is expensive.
     -- This should be compiled as a function which takes 'args' first,
     -- then 'reverse scope'.
     -- (Sorry for the awkward API - it's to do with how the indices are
     -- arranged for the variables, and it oculd be expensive to reshuffle them!
     -- See Compiler.ANF for an example of how they get resolved to names)
     MkLFun : (args : List Name) -> -- function arguments
              (scope : List Name) -> -- outer scope
              Lifted (scope ++ args) -> LiftedDef
     MkLCon : (tag : Maybe Int) -> (arity : Nat) -> (nt : Maybe Nat) -> LiftedDef
     MkLForeign : (ccs : List String) ->
                  (fargs : List CFType) ->
                  CFType ->
                  LiftedDef
     MkLError : Lifted [] -> LiftedDef

mutual
  export
  {vs : _} -> Show (Lifted vs) where
    show (LLocal {idx} _ p) = "!" ++ show (nameAt p)
    show (LAppName fc n args)
        = show n ++ "(" ++ showSep ", " (map show args) ++ ")"
    show (LUnderApp fc n m args)
        = "<" ++ show n ++ " underapp " ++ show m ++ ">(" ++
          showSep ", " (map show args) ++ ")"
    show (LApp fc c arg)
        = show c ++ " @ (" ++ show arg ++ ")"
    show (LLet fc x val sc)
        = "%let " ++ show x ++ " = " ++ show val ++ " in " ++ show sc
    show (LCon fc n t args)
        = "%con " ++ show n ++ "(" ++ showSep ", " (map show args) ++ ")"
    show (LOp fc op args)
        = "%op " ++ show op ++ "(" ++ showSep ", " (toList (map show args)) ++ ")"
    show (LExtPrim fc p args)
        = "%extprim " ++ show p ++ "(" ++ showSep ", " (map show args) ++ ")"
    show (LConCase fc sc alts def)
        = "%case " ++ show sc ++ " of { "
             ++ showSep "| " (map show alts) ++ " " ++ show def
    show (LConstCase fc sc alts def)
        = "%case " ++ show sc ++ " of { "
             ++ showSep "| " (map show alts) ++ " " ++ show def
    show (LPrimVal _ x) = show x
    show (LErased _) = "___"
    show (LCrash _ x) = "%CRASH(" ++ show x ++ ")"

  export
  {vs : _} -> Show (LiftedConAlt vs) where
    show (MkLConAlt n t args sc)
        = "%conalt " ++ show n ++
             "(" ++ showSep ", " (map show args) ++ ") => " ++ show sc

  export
  {vs : _} -> Show (LiftedConstAlt vs) where
    show (MkLConstAlt c sc)
        = "%constalt(" ++ show c ++ ") => " ++ show sc

export
Show LiftedDef where
  show (MkLFun args scope exp)
      = show args ++ show (reverse scope) ++ ": " ++ show exp
  show (MkLCon tag arity pos)
      = "Constructor tag " ++ show tag ++ " arity " ++ show arity ++
        maybe "" (\n => " (newtype by " ++ show n ++ ")") pos
  show (MkLForeign ccs args ret)
      = "Foreign call " ++ show ccs ++ " " ++
        show args ++ " -> " ++ show ret
  show (MkLError exp) = "Error: " ++ show exp


data Lifts : Type where

record LDefs where
  constructor MkLDefs
  basename : Name -- top level name we're lifting from
  defs : List (Name, LiftedDef) -- new definitions we made
  nextName : Int -- name of next definition to lift

genName : {auto l : Ref Lifts LDefs} ->
          Core Name
genName
    = do ldefs <- get Lifts
         let i = nextName ldefs
         put Lifts (record { nextName = i + 1 } ldefs)
         pure $ mkName (basename ldefs) i
  where
    mkName : Name -> Int -> Name
    mkName (NS ns b) i = NS ns (mkName b i)
    mkName (UN n) i = MN n i
    mkName (DN _ n) i = mkName n i
    mkName (CaseBlock outer inner) i = MN ("case block in " ++ outer ++ " (" ++ show inner ++ ")") i
    mkName (WithBlock outer inner) i = MN ("with block in " ++ outer ++ " (" ++ show inner ++ ")") i
    mkName n i = MN (show n) i

unload : FC -> Lifted vars -> List (Lifted vars) -> Core (Lifted vars)
unload fc f [] = pure f
unload fc f (a :: as) = unload fc (LApp fc f a) as

mutual
  makeLam : {auto l : Ref Lifts LDefs} ->
            {vars : _} ->
            FC -> (bound : List Name) ->
            CExp (bound ++ vars) -> Core (Lifted vars)
  makeLam fc bound (CLam _ x sc') = makeLam fc (x :: bound) sc'
  makeLam {vars} fc bound sc
      = do scl <- liftExp sc
           n <- genName
           ldefs <- get Lifts
           put Lifts (record { defs $= ((n, MkLFun vars bound scl) ::) } ldefs)
           -- TODO: an optimisation here would be to spot which variables
           -- aren't used in the new definition, and not abstract over them
           -- in the new definition. Given that we have to do some messing
           -- about with indices anyway, it's probably not costly to do.
           pure $ LUnderApp fc n (length bound) (allVars vars)
    where
      allPrfs : (vs : List Name) -> List (Var vs)
      allPrfs [] = []
      allPrfs (v :: vs) = MkVar First :: map weaken (allPrfs vs)

      -- apply to all the variables. 'First' will be first in the last, which
      -- is good, because the most recently bound name is the first argument to
      -- the resulting function
      allVars : (vs : List Name) -> List (Lifted vs)
      allVars vs = map (\ (MkVar p) => LLocal fc p) (allPrfs vs)

  liftExp : {vars : _} ->
            {auto l : Ref Lifts LDefs} ->
            CExp vars -> Core (Lifted vars)
  liftExp (CLocal fc prf) = pure $ LLocal fc prf
  liftExp (CRef fc n) = pure $ LAppName fc n [] -- probably shouldn't happen!
  liftExp (CLam fc x sc) = makeLam fc [x] sc
  liftExp (CLet fc x _ val sc) = pure $ LLet fc x !(liftExp val) !(liftExp sc)
  liftExp (CApp fc (CRef _ n) args) -- names are applied exactly in compileExp
      = pure $ LAppName fc n !(traverse liftExp args)
  liftExp (CApp fc f args)
      = unload fc !(liftExp f) !(traverse liftExp args)
  liftExp (CCon fc n t args) = pure $ LCon fc n t !(traverse liftExp args)
  liftExp (COp fc op args)
      = pure $ LOp fc op !(traverseArgs args)
    where
      traverseArgs : Vect n (CExp vars) -> Core (Vect n (Lifted vars))
      traverseArgs [] = pure []
      traverseArgs (a :: as) = pure $ !(liftExp a) :: !(traverseArgs as)
  liftExp (CExtPrim fc p args) = pure $ LExtPrim fc p !(traverse liftExp args)
  liftExp (CForce fc tm) = liftExp (CApp fc tm [CErased fc])
  liftExp (CDelay fc tm) = liftExp (CLam fc (MN "act" 0) (weaken tm))
  liftExp (CConCase fc sc alts def)
      = pure $ LConCase fc !(liftExp sc) !(traverse liftConAlt alts)
                           !(traverseOpt liftExp def)
    where
      liftConAlt : CConAlt vars -> Core (LiftedConAlt vars)
      liftConAlt (MkConAlt n t args sc) = pure $ MkLConAlt n t args !(liftExp sc)
  liftExp (CConstCase fc sc alts def)
      = pure $ LConstCase fc !(liftExp sc) !(traverse liftConstAlt alts)
                             !(traverseOpt liftExp def)
    where
      liftConstAlt : CConstAlt vars -> Core (LiftedConstAlt vars)
      liftConstAlt (MkConstAlt c sc) = pure $ MkLConstAlt c !(liftExp sc)
  liftExp (CPrimVal fc c) = pure $ LPrimVal fc c
  liftExp (CErased fc) = pure $ LErased fc
  liftExp (CCrash fc str) = pure $ LCrash fc str

export
liftBody : {vars : _} ->
           Name -> CExp vars -> Core (Lifted vars, List (Name, LiftedDef))
liftBody n tm
    = do l <- newRef Lifts (MkLDefs n [] 0)
         tml <- liftExp {l} tm
         ldata <- get Lifts
         pure (tml, defs ldata)

lambdaLiftDef : Name -> CDef -> Core (List (Name, LiftedDef))
lambdaLiftDef n (MkFun args exp)
    = do (expl, defs) <- liftBody n exp
         pure ((n, MkLFun args [] expl) :: defs)
lambdaLiftDef n (MkCon t a nt) = pure [(n, MkLCon t a nt)]
lambdaLiftDef n (MkForeign ccs fargs ty) = pure [(n, MkLForeign ccs fargs ty)]
lambdaLiftDef n (MkError exp)
    = do (expl, defs) <- liftBody n exp
         pure ((n, MkLError expl) :: defs)

-- Return the lambda lifted definitions required for the given name.
-- If the name hasn't been compiled yet (via CompileExpr.compileDef) then
-- this will return an empty list
-- An empty list an error, because on success you will always get at least
-- one definition, the lifted definition for the given name.
export
lambdaLift : {auto c : Ref Ctxt Defs} ->
             Name -> Core (List (Name, LiftedDef))
lambdaLift n
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs) | Nothing => pure []
         let Just cexpr = compexpr def              | Nothing => pure []
         lambdaLiftDef n cexpr

module Core.Value

import Core.Context
import Core.Core
import Core.Env
import Core.TT

%default covering

public export
data EvalOrder = CBV | CBN

public export
record EvalOpts where
  constructor MkEvalOpts
  holesOnly : Bool -- only evaluate hole solutions
  argHolesOnly : Bool -- only evaluate holes which are relevant arguments
  removeAs : Bool -- reduce 'as' patterns (don't do this on LHS)
  evalAll : Bool -- evaluate everything, including private names
  tcInline : Bool -- inline for totality checking
  fuel : Maybe Nat -- Limit for recursion depth
  reduceLimit : List (Name, Nat) -- reduction limits for given names. If not
                     -- present, no limit
  strategy : EvalOrder

export
defaultOpts : EvalOpts
defaultOpts = MkEvalOpts False False True False False Nothing [] CBN

export
withHoles : EvalOpts
withHoles = MkEvalOpts True True False False False Nothing [] CBN

export
withAll : EvalOpts
withAll = MkEvalOpts False False True True False Nothing [] CBN

export
withArgHoles : EvalOpts
withArgHoles = MkEvalOpts False True False False False Nothing [] CBN

export
tcOnly : EvalOpts
tcOnly = { tcInline := True } withArgHoles

export
onLHS : EvalOpts
onLHS = { removeAs := False } defaultOpts

export
cbn : EvalOpts
cbn = defaultOpts

export
cbv : EvalOpts
cbv = { strategy := CBV } defaultOpts

mutual
  public export
  data LocalEnv : SnocList Name -> SnocList Name -> Type where
       Nil  : LocalEnv free [<]
       (::) : Closure free -> LocalEnv free vars -> LocalEnv free (vars :< x)

  public export
  data Closure : SnocList Name -> Type where
       MkClosure : {vars : _} ->
                   (opts : EvalOpts) ->
                   LocalEnv free vars ->
                   Env Term free ->
                   Term (free ++ vars) -> Closure free
       MkNFClosure : EvalOpts -> Env Term free -> NF free -> Closure free

  -- The head of a value: things you can apply arguments to
  public export
  data NHead : SnocList Name -> Type where
       NLocal : Maybe Bool -> (idx : Nat) -> (0 p : IsVar nm idx vars) ->
                NHead vars
       NRef   : NameType -> Name -> NHead vars
       NMeta  : Name -> Int -> List (Closure vars) -> NHead vars


  -- Values themselves. 'Closure' is an unevaluated thunk, which means
  -- we can wait until necessary to reduce constructor arguments
  public export
  data NF : SnocList Name -> Type where
       NBind    : FC -> (x : Name) -> Binder (Closure vars) ->
                  (Defs -> Closure vars -> Core (NF vars)) -> NF vars
       -- Each closure is associated with the file context of the App node that
       -- had it as an argument. It's necessary so as to not lose file context
       -- information when creating the normal form.
       NApp     : FC -> NHead vars -> SnocList (FC, Closure vars) -> NF vars
       NDCon    : FC -> Name -> (tag : Int) -> (arity : Nat) ->
                  SnocList (FC, Closure vars) -> NF vars
       NTCon    : FC -> Name -> (tag : Int) -> (arity : Nat) ->
                  SnocList (FC, Closure vars) -> NF vars
       NAs      : FC -> UseSide -> NF vars -> NF vars -> NF vars
       NDelayed : FC -> LazyReason -> NF vars -> NF vars
       NDelay   : FC -> LazyReason -> Closure vars -> Closure vars -> NF vars
       NForce   : FC -> LazyReason -> NF vars -> SnocList (FC, Closure vars) -> NF vars
       NPrimVal : FC -> Constant -> NF vars
       NErased  : FC -> WhyErased (NF vars) -> NF vars
       NType    : FC -> Name -> NF vars

%name LocalEnv lenv
%name Closure cl
%name NHead hd
%name NF nf

export
ntCon : FC -> Name -> Int -> Nat -> SnocList (FC, Closure vars) -> NF vars
-- Part of the machinery for matching on types - I believe this won't affect
-- universe checking so put a dummy name.
ntCon fc (UN (Basic "Type")) tag Z [<] = NType fc (MN "top" 0)
ntCon fc n tag Z [<] = case isConstantType n of
  Just c => NPrimVal fc $ PrT c
  Nothing => NTCon fc n tag Z [<]
ntCon fc n tag arity args = NTCon fc n tag arity args

export
getLoc : NF vars -> FC
getLoc (NBind fc _ _ _) = fc
getLoc (NApp fc _ _) = fc
getLoc (NDCon fc _ _ _ _) = fc
getLoc (NTCon fc _ _ _ _) = fc
getLoc (NAs fc _ _ _) = fc
getLoc (NDelayed fc _ _) = fc
getLoc (NDelay fc _ _ _) = fc
getLoc (NForce fc _ _ _) = fc
getLoc (NPrimVal fc _) = fc
getLoc (NErased fc i) = fc
getLoc (NType fc _) = fc

export
{free : _} -> Show (NHead free) where
  show (NLocal _ idx p) = show (nameAt p) ++ "[" ++ show idx ++ "]"
  show (NRef _ n) = show n
  show (NMeta n _ args) = "?" ++ show n ++ "_[" ++ show (length args) ++ " closures]"

Show (Closure free) where
  show _ = "[closure]"

export
HasNames (NHead free) where
  full defs (NRef nt n) = NRef nt <$> full defs n
  full defs hd = pure hd

  resolved defs (NRef nt n) = NRef nt <$> resolved defs n
  resolved defs hd = pure hd

export
HasNames (NF free) where
  full defs (NBind fc x bd f) = pure $ NBind fc x bd f
  full defs (NApp fc hd xs) = pure $ NApp fc !(full defs hd) xs
  full defs (NDCon fc n tag arity xs) = pure $ NDCon fc !(full defs n) tag arity xs
  full defs (NTCon fc n tag arity xs) = pure $ NTCon fc !(full defs n) tag arity xs
  full defs (NAs fc side nf nf1) = pure $ NAs fc side !(full defs nf) !(full defs nf1)
  full defs (NDelayed fc lz nf) = pure $ NDelayed fc lz !(full defs nf)
  full defs (NDelay fc lz cl cl1) = pure $ NDelay fc lz cl cl1
  full defs (NForce fc lz nf xs) = pure $ NForce fc lz !(full defs nf) xs
  full defs (NPrimVal fc cst) = pure $ NPrimVal fc cst
  full defs (NErased fc imp) = pure $ NErased fc imp
  full defs (NType fc n) = pure $ NType fc !(full defs n)

  resolved defs (NBind fc x bd f) = pure $ NBind fc x bd f
  resolved defs (NApp fc hd xs) = pure $ NApp fc !(resolved defs hd) xs
  resolved defs (NDCon fc n tag arity xs) = pure $ NDCon fc !(resolved defs n) tag arity xs
  resolved defs (NTCon fc n tag arity xs) = pure $ NTCon fc !(resolved defs n) tag arity xs
  resolved defs (NAs fc side nf nf1) = pure $ NAs fc side !(resolved defs nf) !(resolved defs nf1)
  resolved defs (NDelayed fc lz nf) = pure $ NDelayed fc lz !(resolved defs nf)
  resolved defs (NDelay fc lz cl cl1) = pure $ NDelay fc lz cl cl1
  resolved defs (NForce fc lz nf xs) = pure $ NForce fc lz !(resolved defs nf) xs
  resolved defs (NPrimVal fc cst) = pure $ NPrimVal fc cst
  resolved defs (NErased fc imp) = pure $ NErased fc imp
  resolved defs (NType fc n) = pure $ NType fc !(resolved defs n)

export
covering
{free : _} -> Show (NF free) where
  show (NBind _ x (Lam _ c info ty) _)
    = "\\" ++ withPiInfo info (showCount c ++ show x ++ " : " ++ show ty) ++
      " => [closure]"
  show (NBind _ x (Let _ c val ty) _)
    = "let " ++ showCount c ++ show x ++ " : " ++ show ty ++
      " = " ++ show val ++ " in [closure]"
  show (NBind _ x (Pi _ c info ty) _)
    = withPiInfo info (showCount c ++ show x ++ " : " ++ show ty) ++
      " -> [closure]"
  show (NBind _ x (PVar _ c info ty) _)
    = withPiInfo info ("pat " ++ showCount c ++ show x ++ " : " ++ show ty) ++
      " => [closure]"
  show (NBind _ x (PLet _ c val ty) _)
    = "plet " ++ showCount c ++ show x ++ " : " ++ show ty ++
      " = " ++ show val ++ " in [closure]"
  show (NBind _ x (PVTy _ c ty) _)
    = "pty " ++ showCount c ++ show x ++ " : " ++ show ty ++
      " => [closure]"
  show (NApp _ hd args) = show hd ++ " [" ++ show (length args) ++ " closures]"
  show (NDCon _ n _ _ args) = show n ++ " [" ++ show (length args) ++ " closures]"
  show (NTCon _ n _ _ args) = show n ++ " [" ++ show (length args) ++ " closures]"
  show (NAs _ _ n tm) = show n ++ "@" ++ show tm
  show (NDelayed _ _ tm) = "%Delayed " ++ show tm
  show (NDelay _ _ _ _) = "%Delay [closure]"
  show (NForce _ _ tm args) = "%Force " ++ show tm ++ " [" ++ show (length args) ++ " closures]"
  show (NPrimVal _ c) = show c
  show (NErased _ _) = "[__]"
  show (NType _ _) = "Type"

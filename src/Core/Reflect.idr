module Core.Reflect

import Algebra.Semiring
import Data.List1

import Core.Context
import Core.Env
import Core.Normalise
import Core.TT
import Core.Value

%default covering

public export
interface Reify a where
  reify : {auto c : Ref Ctxt Defs} ->
          {vars : _} ->
          Defs -> NF vars -> Core a

public export
interface Reflect a where
  reflect : {vars : _} ->
            FC -> Defs -> (onLHS : Bool) ->
            Env Term vars -> a -> Core (Term vars)

export
getCon : {vars : _} ->
         FC -> Defs -> Name -> Core (Term vars)
getCon fc defs n
    = case !(lookupDefExact n (gamma defs)) of
           Just (DCon t a _) => resolved (gamma defs) (Ref fc (DataCon t a) n)
           Just (TCon t a _ _ _ _ _ _) => resolved (gamma defs) (Ref fc (TyCon t a) n)
           Just _ => resolved (gamma defs) (Ref fc Func n)
           _ => throw (UndefinedName fc n)

export
appCon : {vars : _} ->
         FC -> Defs -> Name -> List (Term vars) -> Core (Term vars)
appCon fc defs n args
    = do fn <- getCon fc defs n
         resolved (gamma defs) (apply fc fn args)

export
preludetypes : String -> Name
preludetypes n = NS typesNS (UN n)

export
basics : String -> Name
basics n = NS basicsNS (UN n)

export
builtin : String -> Name
builtin n = NS builtinNS (UN n)

export
primio : String -> Name
primio n = NS primIONS (UN n)

export
reflection : String -> Name
reflection n = NS reflectionNS (UN n)

export
reflectiontt : String -> Name
reflectiontt n = NS reflectionTTNS (UN n)

export
reflectionttimp : String -> Name
reflectionttimp n = NS reflectionTTImpNS (UN n)

export
cantReify : NF vars -> String -> Core a
cantReify val ty
    = throw (GenericMsg (getLoc val) ("Can't reify as " ++ ty))

export
cantReflect : FC -> String -> Core a
cantReflect fc ty
    = throw (GenericMsg fc ("Can't reflect as " ++ ty))

export
Reify () where
  reify defs _ = pure ()

export
Reflect () where
  reflect fc defs lhs env _ = getCon fc defs (builtin "MkUnit")

export
Reify String where
  reify defs (NPrimVal _ (Str str)) = pure str
  reify defs val = cantReify val "String"

export
Reflect String where
  reflect fc defs lhs env x = pure (PrimVal fc (Str x))

export
Reify Int where
  reify defs (NPrimVal _ (I v)) = pure v
  reify defs val = cantReify val "Int"

export
Reflect Int where
  reflect fc defs lhs env x = pure (PrimVal fc (I x))

export
Reify Integer where
  reify defs (NPrimVal _ (BI v)) = pure v
  reify defs val = cantReify val "Integer"

export
Reflect Integer where
  reflect fc defs lhs env x = pure (PrimVal fc (BI x))

export
Reify Char where
  reify defs (NPrimVal _ (Ch v)) = pure v
  reify defs val = cantReify val "Char"

export
Reflect Char where
  reflect fc defs lhs env x = pure (PrimVal fc (Ch x))

export
Reify Double where
  reify defs (NPrimVal _ (Db v)) = pure v
  reify defs val = cantReify val "Double"

export
Reflect Double where
  reflect fc defs lhs env x = pure (PrimVal fc (Db x))

export
Reify Bool where
  reify defs val@(NDCon _ n _ _ _)
      = case !(full (gamma defs) n) of
            NS _ (UN "True") => pure True
            NS _ (UN "False") => pure False
            _ => cantReify val "Bool"
  reify defs val = cantReify val "Bool"

export
Reflect Bool where
  reflect fc defs lhs env True = getCon fc defs (basics "True")
  reflect fc defs lhs env False = getCon fc defs (basics "False")

export
Reify Nat where
  reify defs val@(NDCon _ n _ _ args)
      = case (!(full (gamma defs) n), args) of
             (NS _ (UN "Z"), _) => pure Z
             (NS _ (UN "S"), [k])
                 => do k' <- reify defs !(evalClosure defs k)
                       pure (S k')
             _ => cantReify val "Nat"
  reify defs val = cantReify val "Nat"

export
Reflect Nat where
  reflect fc defs lhs env Z = getCon fc defs (preludetypes "Z")
  reflect fc defs lhs env (S k)
      = do k' <- reflect fc defs lhs env k
           appCon fc defs (preludetypes "S") [k']

export
Reify a => Reify (List a) where
  reify defs val@(NDCon _ n _ _ args)
      = case (!(full (gamma defs) n), args) of
             (NS _ (UN "Nil"), _) => pure []
             (NS _ (UN "::"), [_, x, xs])
                  => do x' <- reify defs !(evalClosure defs x)
                        xs' <- reify defs !(evalClosure defs xs)
                        pure (x' :: xs')
             _ => cantReify val "List"
  reify defs val = cantReify val "List"

export
Reflect a => Reflect (List a) where
  reflect fc defs lhs env [] = appCon fc defs (preludetypes "Nil") [Erased fc False]
  reflect fc defs lhs env (x :: xs)
      = do x' <- reflect fc defs lhs env x
           xs' <- reflect fc defs lhs env xs
           appCon fc defs (preludetypes "::") [Erased fc False, x', xs']

export
Reify a => Reify (List1 a) where
  reify defs val@(NDCon _ n _ _ [_, x, xs])
      = case !(full (gamma defs) n) of
             NS _ (UN ":::")
                  => do x' <- reify defs !(evalClosure defs x)
                        xs' <- reify defs !(evalClosure defs xs)
                        pure (x' ::: xs')
             _ => cantReify val "List1"
  reify defs val = cantReify val "List1"

export
Reflect a => Reflect (List1 a) where
  reflect fc defs lhs env (x ::: xs)
      = do x' <- reflect fc defs lhs env x
           xs' <- reflect fc defs lhs env xs
           appCon fc defs (NS (mkNamespace "Data.List1") (UN ":::")) [Erased fc False, x', xs']

export
Reify a => Reify (Maybe a) where
  reify defs val@(NDCon _ n _ _ args)
      = case (!(full (gamma defs) n), args) of
             (NS _ (UN "Nothing"), _) => pure Nothing
             (NS _ (UN "Just"), [_, x])
                  => do x' <- reify defs !(evalClosure defs x)
                        pure (Just x')
             _ => cantReify val "Maybe"
  reify defs val = cantReify val "Maybe"

export
Reflect a => Reflect (Maybe a) where
  reflect fc defs lhs env Nothing = appCon fc defs (preludetypes "Nothing") [Erased fc False]
  reflect fc defs lhs env (Just x)
      = do x' <- reflect fc defs lhs env x
           appCon fc defs (preludetypes "Just") [Erased fc False, x']

export
(Reify a, Reify b) => Reify (a, b) where
  reify defs val@(NDCon _ n _ _ [_, _, x, y])
      = case (!(full (gamma defs) n)) of
             NS _ (UN "MkPair")
                 => do x' <- reify defs !(evalClosure defs x)
                       y' <- reify defs !(evalClosure defs y)
                       pure (x', y')
             _ => cantReify val "Pair"
  reify defs val = cantReify val "Pair"

export
(Reflect a, Reflect b) => Reflect (a, b) where
  reflect fc defs lhs env (x, y)
      = do x' <- reflect fc defs lhs env x
           y' <- reflect fc defs lhs env y
           appCon fc defs (builtin "MkPair") [Erased fc False, Erased fc False, x', y']

export
Reify Namespace where
  reify defs val@(NDCon _ n _ _ [ns])
    = case (!(full (gamma defs) n)) of
        NS _ (UN "MkNS")
          => do ns' <- reify defs !(evalClosure defs ns)
                pure (unsafeFoldNamespace ns')
        _ => cantReify val "Namespace"
  reify defs val = cantReify val "Namespace"

export
Reflect Namespace where
  reflect fc defs lhs env ns
    = do ns' <- reflect fc defs lhs env (unsafeUnfoldNamespace ns)
         appCon fc defs (reflectiontt "MkNS") [ns']

export
Reify Name where
  reify defs val@(NDCon _ n _ _ args)
      = case (!(full (gamma defs) n), args) of
             (NS _ (UN "UN"), [str])
                 => do str' <- reify defs !(evalClosure defs str)
                       pure (UN str')
             (NS _ (UN "MN"), [str, i])
                 => do str' <- reify defs !(evalClosure defs str)
                       i' <- reify defs !(evalClosure defs i)
                       pure (MN str' i')
             (NS _ (UN "NS"), [ns, n])
                 => do ns' <- reify defs !(evalClosure defs ns)
                       n' <- reify defs !(evalClosure defs n)
                       pure (NS ns' n')
             (NS _ (UN "DN"), [str, n])
                 => do str' <- reify defs !(evalClosure defs str)
                       n' <- reify defs !(evalClosure defs n)
                       pure (DN str' n')
             (NS _ (UN "RF"), [str])
                 => do str' <- reify defs !(evalClosure defs str)
                       pure (RF str')
             _ => cantReify val "Name"
  reify defs val = cantReify val "Name"

export
Reflect Name where
  reflect fc defs lhs env (UN x)
      = do x' <- reflect fc defs lhs env x
           appCon fc defs (reflectiontt "UN") [x']
  reflect fc defs lhs env (MN x i)
      = do x' <- reflect fc defs lhs env x
           i' <- reflect fc defs lhs env i
           appCon fc defs (reflectiontt "MN") [x', i']
  reflect fc defs lhs env (NS ns n)
      = do ns' <- reflect fc defs lhs env ns
           n' <- reflect fc defs lhs env n
           appCon fc defs (reflectiontt "NS") [ns', n']
  reflect fc defs lhs env (DN str n)
      = do str' <- reflect fc defs lhs env str
           n' <- reflect fc defs lhs env n
           appCon fc defs (reflectiontt "DN") [str', n']
  reflect fc defs lhs env (RF x)
      = do x' <- reflect fc defs lhs env x
           appCon fc defs (reflectiontt "RF") [x']
  reflect fc defs lhs env (Resolved i)
      = case !(full (gamma defs) (Resolved i)) of
             Resolved _ => cantReflect fc "Name"
             n => reflect fc defs lhs env n
  reflect fc defs lhs env val = cantReflect fc "Name"

export
Reify NameType where
  reify defs val@(NDCon _ n _ _ args)
      = case (!(full (gamma defs) n), args) of
             (NS _ (UN "Bound"), _) => pure Bound
             (NS _ (UN "Func"), _) => pure Func
             (NS _ (UN "DataCon"), [t,i])
                  => do t' <- reify defs !(evalClosure defs t)
                        i' <- reify defs !(evalClosure defs i)
                        pure (DataCon t' i')
             (NS _ (UN "TyCon"), [t,i])
                  => do t' <- reify defs !(evalClosure defs t)
                        i' <- reify defs !(evalClosure defs i)
                        pure (TyCon t' i')
             _ => cantReify val "NameType"
  reify defs val = cantReify val "NameType"

export
Reflect NameType where
  reflect fc defs lhs env Bound = getCon fc defs (reflectiontt "Bound")
  reflect fc defs lhs env Func = getCon fc defs (reflectiontt "Func")
  reflect fc defs lhs env (DataCon t i)
      = do t' <- reflect fc defs lhs env t
           i' <- reflect fc defs lhs env i
           appCon fc defs (reflectiontt "DataCon") [t', i']
  reflect fc defs lhs env (TyCon t i)
      = do t' <- reflect fc defs lhs env t
           i' <- reflect fc defs lhs env i
           appCon fc defs (reflectiontt "TyCon") [t', i']

export
Reify Constant where
  reify defs val@(NDCon _ n _ _ args)
      = case (!(full (gamma defs) n), args) of
             (NS _ (UN "I"), [x])
                  => do x' <- reify defs !(evalClosure defs x)
                        pure (I x')
             (NS _ (UN "BI"), [x])
                  => do x' <- reify defs !(evalClosure defs x)
                        pure (BI x')
             (NS _ (UN "B8"), [x])
                  => do x' <- reify defs !(evalClosure defs x)
                        pure (B8 x')
             (NS _ (UN "B16"), [x])
                  => do x' <- reify defs !(evalClosure defs x)
                        pure (B16 x')
             (NS _ (UN "B32"), [x])
                  => do x' <- reify defs !(evalClosure defs x)
                        pure (B32 x')
             (NS _ (UN "B64"), [x])
                  => do x' <- reify defs !(evalClosure defs x)
                        pure (B64 x')
             (NS _ (UN "Str"), [x])
                  => do x' <- reify defs !(evalClosure defs x)
                        pure (Str x')
             (NS _ (UN "Ch"), [x])
                  => do x' <- reify defs !(evalClosure defs x)
                        pure (Ch x')
             (NS _ (UN "Db"), [x])
                  => do x' <- reify defs !(evalClosure defs x)
                        pure (Db x')
             (NS _ (UN "WorldVal"), [])
                  => pure WorldVal
             (NS _ (UN "IntType"), [])
                  => pure IntType
             (NS _ (UN "IntegerType"), [])
                  => pure IntegerType
             (NS _ (UN "Bits8Type"), [])
                  => pure Bits8Type
             (NS _ (UN "Bits16Type"), [])
                  => pure Bits16Type
             (NS _ (UN "Bits32Type"), [])
                  => pure Bits32Type
             (NS _ (UN "Bits64Type"), [])
                  => pure Bits64Type
             (NS _ (UN "StringType"), [])
                  => pure StringType
             (NS _ (UN "CharType"), [])
                  => pure CharType
             (NS _ (UN "DoubleType"), [])
                  => pure DoubleType
             (NS _ (UN "WorldType"), [])
                  => pure WorldType
             _ => cantReify val "Constant"
  reify defs val = cantReify val "Constant"

export
Reflect Constant where
  reflect fc defs lhs env (I x)
      = do x' <- reflect fc defs lhs env x
           appCon fc defs (reflectiontt "I") [x']
  reflect fc defs lhs env (BI x)
      = do x' <- reflect fc defs lhs env x
           appCon fc defs (reflectiontt "BI") [x']
  reflect fc defs lhs env (B8 x)
      = do x' <- reflect fc defs lhs env x
           appCon fc defs (reflectiontt "B8") [x']
  reflect fc defs lhs env (B16 x)
      = do x' <- reflect fc defs lhs env x
           appCon fc defs (reflectiontt "B16") [x']
  reflect fc defs lhs env (B32 x)
      = do x' <- reflect fc defs lhs env x
           appCon fc defs (reflectiontt "B32") [x']
  reflect fc defs lhs env (B64 x)
      = do x' <- reflect fc defs lhs env x
           appCon fc defs (reflectiontt "B64") [x']
  reflect fc defs lhs env (Str x)
      = do x' <- reflect fc defs lhs env x
           appCon fc defs (reflectiontt "Str") [x']
  reflect fc defs lhs env (Ch x)
      = do x' <- reflect fc defs lhs env x
           appCon fc defs (reflectiontt "Ch") [x']
  reflect fc defs lhs env (Db x)
      = do x' <- reflect fc defs lhs env x
           appCon fc defs (reflectiontt "Db") [x']
  reflect fc defs lhs env WorldVal
      = getCon fc defs (reflectiontt "WorldVal")
  reflect fc defs lhs env IntType
      = getCon fc defs (reflectiontt "IntType")
  reflect fc defs lhs env IntegerType
      = getCon fc defs (reflectiontt "IntegerType")
  reflect fc defs lhs env Bits8Type
      = getCon fc defs (reflectiontt "Bits8Type")
  reflect fc defs lhs env Bits16Type
      = getCon fc defs (reflectiontt "Bits16Type")
  reflect fc defs lhs env Bits32Type
      = getCon fc defs (reflectiontt "Bits32Type")
  reflect fc defs lhs env Bits64Type
      = getCon fc defs (reflectiontt "Bits64Type")
  reflect fc defs lhs env StringType
      = getCon fc defs (reflectiontt "StringType")
  reflect fc defs lhs env CharType
      = getCon fc defs (reflectiontt "CharType")
  reflect fc defs lhs env DoubleType
      = getCon fc defs (reflectiontt "DoubleType")
  reflect fc defs lhs env WorldType
      = getCon fc defs (reflectiontt "WorldType")

export
Reify Visibility where
  reify defs val@(NDCon _ n _ _ _)
      = case !(full (gamma defs) n) of
             NS _ (UN "Private") => pure Private
             NS _ (UN "Export") => pure Export
             NS _ (UN "Public") => pure Public
             _ => cantReify val "Visibility"
  reify defs val = cantReify val "Visibility"

export
Reflect Visibility where
  reflect fc defs lhs env Private = getCon fc defs (reflectiontt "Private")
  reflect fc defs lhs env Export = getCon fc defs (reflectiontt "Export")
  reflect fc defs lhs env Public = getCon fc defs (reflectiontt "Public")

export
Reify TotalReq where
  reify defs val@(NDCon _ n _ _ _)
      = case !(full (gamma defs) n) of
             NS _ (UN "Total") => pure Total
             NS _ (UN "CoveringOnly") => pure CoveringOnly
             NS _ (UN "PartialOK") => pure PartialOK
             _ => cantReify val "TotalReq"
  reify defs val = cantReify val "TotalReq"

export
Reflect TotalReq where
  reflect fc defs lhs env Total = getCon fc defs (reflectiontt "Total")
  reflect fc defs lhs env CoveringOnly = getCon fc defs (reflectiontt "CoveringOnly")
  reflect fc defs lhs env PartialOK = getCon fc defs (reflectiontt "PartialOK")

export
Reify RigCount where
  reify defs val@(NDCon _ n _ _ _)
      = case !(full (gamma defs) n) of
             NS _ (UN "M0") => pure erased
             NS _ (UN "M1") => pure linear
             NS _ (UN "MW") => pure top
             _ => cantReify val "Count"
  reify defs val = cantReify val "Count"

export
Reflect RigCount where
  reflect fc defs lhs env r
      = elimSemi (getCon fc defs (reflectiontt "M0"))
                 (getCon fc defs (reflectiontt "M1"))
                 (const (getCon fc defs (reflectiontt "MW")))
                 r

export
Reify t => Reify (PiInfo t) where
  reify defs val@(NDCon _ n _ _ args)
      = case (!(full (gamma defs) n), args) of
             (NS _ (UN "ImplicitArg"), _) => pure Implicit
             (NS _ (UN "ExplicitArg"), _) => pure Explicit
             (NS _ (UN "AutoImplicit"), _) => pure AutoImplicit
             (NS _ (UN "DefImplicit"), [_, t])
                 => do t' <- reify defs !(evalClosure defs t)
                       pure (DefImplicit t')
             _ => cantReify val "PiInfo"
  reify defs val = cantReify val "PiInfo"

export
Reflect t => Reflect (PiInfo t) where
  reflect fc defs lhs env Implicit
      = appCon fc defs (reflectiontt "ImplicitArg") [Erased fc False]
  reflect fc defs lhs env Explicit
      = appCon fc defs (reflectiontt "ExplicitArg") [Erased fc False]
  reflect fc defs lhs env AutoImplicit
      = appCon fc defs (reflectiontt "AutoImplicit") [Erased fc False]
  reflect fc defs lhs env (DefImplicit t)
      = do t' <- reflect fc defs lhs env t
           appCon fc defs (reflectiontt "DefImplicit") [Erased fc False, t']

export
Reify LazyReason where
  reify defs val@(NDCon _ n _ _ _)
      = case !(full (gamma defs) n) of
             NS _ (UN "LInf") => pure LInf
             NS _ (UN "LLazy") => pure LLazy
             NS _ (UN "LUnknown") => pure LUnknown
             _ => cantReify val "LazyReason"
  reify defs val = cantReify val "LazyReason"

export
Reflect LazyReason where
  reflect fc defs lhs env LInf = getCon fc defs (reflectiontt "LInf")
  reflect fc defs lhs env LLazy = getCon fc defs (reflectiontt "LLazy")
  reflect fc defs lhs env LUnknown = getCon fc defs (reflectiontt "LUnknown")

export
Reify FC where
  reify defs val@(NDCon _ n _ _ args)
      = case (!(full (gamma defs) n), args) of
             (NS _ (UN "MkFC"), [fn, start, end])
                   => do fn' <- reify defs !(evalClosure defs fn)
                         start' <- reify defs !(evalClosure defs start)
                         end' <- reify defs !(evalClosure defs end)
                         pure (MkFC fn' start' end')
             (NS _ (UN "EmptyFC"), _) => pure EmptyFC
             _ => cantReify val "FC"
  reify defs val = cantReify val "FC"

export
Reflect FC where
  reflect fc defs True env _ = pure $ Erased fc False
  reflect fc defs lhs env (MkFC fn start end)
      = do fn' <- reflect fc defs lhs env fn
           start' <- reflect fc defs lhs env start
           end' <- reflect fc defs lhs env end
           appCon fc defs (reflectiontt "MkFC") [fn', start', end']
  reflect fc defs lhs env EmptyFC = getCon fc defs (reflectiontt "EmptyFC")

{-
-- Reflection of well typed terms: We don't reify terms because that involves
-- type checking, but we can reflect them

-- TODO: Do we need this? Fix reify if we do.

export
Reflect (IsVar name idx vs) where
  reflect fc defs lhs env First
      = appCon fc defs (reflectiontt "First") [Erased fc False, Erased fc False]
  reflect fc defs lhs env (Later p)
      = do p' <- reflect fc defs lhs env p
           appCon fc defs (reflectiontt "Later")
                  [Erased fc False, Erased fc False,
                   Erased fc False, Erased fc False, p']

-- Assume terms are normalised so there's not Let bindings in particular
export
Reflect (Term vs) where
  reflect fc defs lhs env (Local {name} lfc _ idx prf)
      = do lfc' <- reflect fc defs lhs env lfc
           idx' <- reflect fc defs lhs env idx
           appCon fc defs (reflectiontt "Local")
                  [Erased fc False, Erased fc False, lfc', idx', Erased fc False]
  reflect fc defs lhs env (Ref rfc nt n)
      = do rfc' <- reflect fc defs lhs env rfc
           nt' <- reflect fc defs lhs env nt
           n' <- reflect fc defs lhs env n
           appCon fc defs (reflectiontt "Ref")
                  [Erased fc False, rfc', nt', n']
  reflect fc defs lhs env (Bind bfc x (Pi c p ty) sc)
      = do bfc' <- reflect fc defs lhs env bfc
           x' <- reflect fc defs lhs env x
           c' <- reflect fc defs lhs env c
           p' <- reflect fc defs lhs env p
           ty' <- reflect fc defs lhs env ty
           sc' <- reflect fc defs lhs env sc
           appCon fc defs (reflectiontt "Pi")
                  [Erased fc False, bfc', c', p', x', ty', sc']
  reflect fc defs lhs env (Bind bfc x (Lam c p ty) sc)
      = do bfc' <- reflect fc defs lhs env bfc
           x' <- reflect fc defs lhs env x
           c' <- reflect fc defs lhs env c
           p' <- reflect fc defs lhs env p
           ty' <- reflect fc defs lhs env ty
           sc' <- reflect fc defs lhs env sc
           appCon fc defs (reflectiontt "Lam")
                  [Erased fc False, bfc', c', p', x', ty', sc']
  reflect fc defs lhs env (App afc fn arg)
      = do afc' <- reflect fc defs lhs env afc
           fn' <- reflect fc defs lhs env fn
           arg' <- reflect fc defs lhs env arg
           appCon fc defs (reflectiontt "App")
                  [Erased fc False, afc', fn', arg']
  reflect fc defs lhs env (TDelayed dfc r tm)
      = do dfc' <- reflect fc defs lhs env dfc
           r' <- reflect fc defs lhs env r
           tm' <- reflect fc defs lhs env tm
           appCon fc defs (reflectiontt "TDelayed")
                  [Erased fc False, dfc', r', tm']
  reflect fc defs lhs env (TDelay dfc r ty tm)
      = do dfc' <- reflect fc defs lhs env dfc
           r' <- reflect fc defs lhs env r
           ty' <- reflect fc defs lhs env ty
           tm' <- reflect fc defs lhs env tm
           appCon fc defs (reflectiontt "TDelay")
                  [Erased fc False, dfc', r', ty', tm']
  reflect fc defs lhs env (TForce dfc r tm)
      = do dfc' <- reflect fc defs lhs env dfc
           r' <- reflect fc defs lhs env r
           tm' <- reflect fc defs lhs env tm
           appCon fc defs (reflectiontt "TForce")
                  [Erased fc False, r', dfc', tm']
  reflect fc defs lhs env (PrimVal pfc c)
      = do pfc' <- reflect fc defs lhs env pfc
           c' <- reflect fc defs lhs env c
           appCon fc defs (reflectiontt "PrimVal")
                  [Erased fc False, pfc', c']
  reflect fc defs lhs env (Erased efc _)
      = do efc' <- reflect fc defs lhs env efc
           appCon fc defs (reflectiontt "Erased")
                  [Erased fc False, efc']
  reflect fc defs lhs env (TType tfc)
      = do tfc' <- reflect fc defs lhs env tfc
           appCon fc defs (reflectiontt "TType")
                  [Erased fc False, tfc']
  reflect fc defs lhs env val = cantReflect fc "Term"
  -}

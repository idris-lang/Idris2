module Core.Reflect

import Data.List1

import Core.Context
import Core.Env
import Core.Normalise
import Core.TT
import Core.Value
import Core.Name.ScopedList

import Libraries.Data.WithDefault

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
preludetypes n = NS typesNS (UN $ Basic n)

export
basics : String -> Name
basics n = NS basicsNS (UN $ Basic n)

export
builtin : String -> Name
builtin n = NS builtinNS (UN $ Basic n)

export
primio : String -> Name
primio n = NS primIONS (UN $ Basic n)

export
reflection : String -> Name
reflection n = NS reflectionNS (UN $ Basic n)

export
reflectiontt : String -> Name
reflectiontt n = NS reflectionTTNS (UN $ Basic n)

export
reflectionttimp : String -> Name
reflectionttimp n = NS reflectionTTImpNS (UN $ Basic n)

export
cantReify : Ref Ctxt Defs => {vars : _} -> NF vars -> String -> Core a
cantReify val ty = do
  logNF "reflection.reify" 10 "Can't reify as \{ty}" (mkEnv emptyFC vars) val
  throw (GenericMsg (getLoc val) ("Can't reify as " ++ ty))

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
Reify Int8 where
  reify defs (NPrimVal _ (I8 v)) = pure v
  reify defs val = cantReify val "Int8"

export
Reflect Int8 where
  reflect fc defs lhs env x = pure (PrimVal fc (I8 x))

export
Reify Int16 where
  reify defs (NPrimVal _ (I16 v)) = pure v
  reify defs val = cantReify val "Int16"

export
Reflect Int16 where
  reflect fc defs lhs env x = pure (PrimVal fc (I16 x))

export
Reify Int32 where
  reify defs (NPrimVal _ (I32 v)) = pure v
  reify defs val = cantReify val "Int32"

export
Reflect Int32 where
  reflect fc defs lhs env x = pure (PrimVal fc (I32 x))

export
Reify Int64 where
  reify defs (NPrimVal _ (I64 v)) = pure v
  reify defs val = cantReify val "Int64"

export
Reflect Int64 where
  reflect fc defs lhs env x = pure (PrimVal fc (I64 x))

export
Reify Bits8 where
  reify defs (NPrimVal _ (B8 v)) = pure v
  reify defs val = cantReify val "Bits8"

export
Reflect Bits8 where
  reflect fc defs lhs env x = pure (PrimVal fc (B8 x))

export
Reify Bits16 where
  reify defs (NPrimVal _ (B16 v)) = pure v
  reify defs val = cantReify val "Bits16"

export
Reflect Bits16 where
  reflect fc defs lhs env x = pure (PrimVal fc (B16 x))

export
Reify Bits32 where
  reify defs (NPrimVal _ (B32 v)) = pure v
  reify defs val = cantReify val "Bits32"

export
Reflect Bits32 where
  reflect fc defs lhs env x = pure (PrimVal fc (B32 x))

export
Reify Bits64 where
  reify defs (NPrimVal _ (B64 v)) = pure v
  reify defs val = cantReify val "Bits64"

export
Reflect Bits64 where
  reflect fc defs lhs env x = pure (PrimVal fc (B64 x))

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
      = case dropAllNS !(full (gamma defs) n) of
            UN (Basic "True") => pure True
            UN (Basic "False") => pure False
            _ => cantReify val "Bool"
  reify defs val = cantReify val "Bool"

export
Reflect Bool where
  reflect fc defs lhs env True = getCon fc defs (basics "True")
  reflect fc defs lhs env False = getCon fc defs (basics "False")

export
Reify Nat where
  reify defs val@(NDCon _ n _ _ args)
      = case (dropAllNS !(full (gamma defs) n), args) of
             (UN (Basic "Z"), _) => pure Z
             (UN (Basic "S"), ((_, k) :%: SLNil))
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
      = case (dropAllNS !(full (gamma defs) n), args) of
             (UN (Basic "Nil"), _) => pure []
             (UN (Basic "::"), (_ :%: (_, x) :%: (_, xs) :%: SLNil))
                  => do x' <- reify defs !(evalClosure defs x)
                        xs' <- reify defs !(evalClosure defs xs)
                        pure (x' :: xs')
             _ => cantReify val "List"
  reify defs val = cantReify val "List"

export
Reify a => Reify (ScopedList a) where
  reify defs val@(NDCon _ n _ _ args)
      = case (dropAllNS !(full (gamma defs) n), args) of
             (UN (Basic "SLNil"), _) => pure SLNil
             (UN (Basic ":%:"), (_ :%: (_, x) :%: (_, xs) :%: SLNil))
                  => do x' <- reify defs !(evalClosure defs x)
                        xs' <- reify defs !(evalClosure defs xs)
                        pure (x' :%: xs')
             _ => cantReify val "ScopedList"
  reify defs val = cantReify val "ScopedList"

export
Reflect a => Reflect (List a) where
  reflect fc defs lhs env [] = appCon fc defs (basics "Nil") [Erased fc Placeholder]
  reflect fc defs lhs env (x :: xs)
      = do x' <- reflect fc defs lhs env x
           xs' <- reflect fc defs lhs env xs
           appCon fc defs (basics "::") [Erased fc Placeholder, x', xs']

export
Reflect a => Reflect (ScopedList a) where
  reflect fc defs lhs env SLNil = appCon fc defs (basics "SLNil") [Erased fc Placeholder]
  reflect fc defs lhs env (x :%: xs)
      = do x' <- reflect fc defs lhs env x
           xs' <- reflect fc defs lhs env xs
           appCon fc defs (basics ":%:") [Erased fc Placeholder, x', xs']

export
Reify a => Reify (List1 a) where
  reify defs val@(NDCon _ n _ _ (_ :%: (_, x) :%: (_, xs) :%: SLNil))
      = case dropAllNS !(full (gamma defs) n) of
             UN (Basic ":::")
                  => do x' <- reify defs !(evalClosure defs x)
                        xs' <- reify defs !(evalClosure defs xs)
                        pure (x' ::: xs')
             _ => cantReify val "List1"
  reify defs val = cantReify val "List1"

export
Reflect a => Reflect (List1 a) where
  reflect fc defs lhs env xxs
      = do x' <- reflect fc defs lhs env (head xxs)
           xs' <- reflect fc defs lhs env (tail xxs)
           appCon fc defs (NS (mkNamespace "Data.List1")
                  (UN $ Basic ":::")) [Erased fc Placeholder, x', xs']

export
Reify a => Reify (SnocList a) where
  reify defs val@(NDCon _ n _ _ args)
      = case (dropAllNS !(full (gamma defs) n), args) of
             (UN (Basic "Lin"), _) => pure [<]
             (UN (Basic ":<"), (_ :%: (_, sx) :%: (_, x) :%: SLNil))
                  => do sx' <- reify defs !(evalClosure defs sx)
                        x' <- reify defs !(evalClosure defs x)
                        pure (sx' :< x')
             _ => cantReify val "SnocList"
  reify defs val = cantReify val "SnocList"

export
Reflect a => Reflect (SnocList a) where
  reflect fc defs lhs env [<] = appCon fc defs (basics "Lin") [Erased fc Placeholder]
  reflect fc defs lhs env (sx :< x)
      = do sx' <- reflect fc defs lhs env sx
           x' <- reflect fc defs lhs env x
           appCon fc defs (basics ":<") [Erased fc Placeholder, sx', x']

export
Reify a => Reify (Maybe a) where
  reify defs val@(NDCon _ n _ _ args)
      = case (dropAllNS !(full (gamma defs) n), args) of
             (UN (Basic "Nothing"), _) => pure Nothing
             (UN (Basic "Just"), (_ :%: (_, x) :%: SLNil))
                  => do x' <- reify defs !(evalClosure defs x)
                        pure (Just x')
             _ => cantReify val "Maybe"
  reify defs val = cantReify val "Maybe"

export
Reflect a => Reflect (Maybe a) where
  reflect fc defs lhs env Nothing = appCon fc defs (preludetypes "Nothing") [Erased fc Placeholder]
  reflect fc defs lhs env (Just x)
      = do x' <- reflect fc defs lhs env x
           appCon fc defs (preludetypes "Just") [Erased fc Placeholder, x']


export
Reify a => Reify (WithDefault a def) where
  reify defs val@(NDCon _ n _ _ args)
      = case (dropAllNS !(full (gamma defs) n), args) of
             (UN (Basic "DefaultedValue"), _) => pure defaulted
             (UN (Basic "SpecifiedValue"), (_ :%: _ :%: (_, x) :%: SLNil))
                  => do x' <- reify defs !(evalClosure defs x)
                        pure (specified x')
             _ => cantReify val "WithDefault"
  reify defs val = cantReify val "WithDefault"

export
Reflect a => Reflect (WithDefault a def) where
  reflect fc defs lhs env def
    = onWithDefault
        (appCon fc defs (reflectionttimp "DefaultedValue") [Erased fc Placeholder, Erased fc Placeholder])
        (\x => do x' <- reflect fc defs lhs env x
                  appCon fc defs (reflectionttimp "SpecifiedValue") [Erased fc Placeholder, Erased fc Placeholder, x'])
        def

export
(Reify a, Reify b) => Reify (a, b) where
  reify defs val@(NDCon _ n _ _ (_ :%: _ :%: (_, x) :%: (_, y) :%: SLNil))
      = case dropAllNS !(full (gamma defs) n) of
             UN (Basic "MkPair")
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
           appCon fc defs (builtin "MkPair") [Erased fc Placeholder, Erased fc Placeholder, x', y']

export
Reify Namespace where
  reify defs val@(NDCon _ n _ _ ((_, ns) :%: SLNil))
    = case dropAllNS !(full (gamma defs) n) of
        UN (Basic "MkNS")
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
Reify ModuleIdent where
  reify defs val@(NDCon _ n _ _ ((_, ns) :%: SLNil))
    = case dropAllNS !(full (gamma defs) n) of
        UN (Basic "MkMI")
          => do ns' <- reify defs !(evalClosure defs ns)
                pure (unsafeFoldModuleIdent ns')
        _ => cantReify val "ModuleIdent"
  reify defs val = cantReify val "ModuleIdent"

export
Reflect ModuleIdent where
  reflect fc defs lhs env ns
    = do ns' <- reflect fc defs lhs env (unsafeUnfoldModuleIdent ns)
         appCon fc defs (reflectiontt "MkMI") [ns']

export
Reify UserName where
  reify defs val@(NDCon _ n _ _ args)
      = case (dropAllNS !(full (gamma defs) n), args) of
             (UN (Basic "Basic"), ((_, str) :%: SLNil))
                 => do str' <- reify defs !(evalClosure defs str)
                       pure (Basic str')
             (UN (Basic "Field"), ((_, str) :%: SLNil))
                 => do str' <- reify defs !(evalClosure defs str)
                       pure (Field str')
             (UN (Basic "Underscore"), SLNil)
                 => pure Underscore
             (NS _ (UN _), _)
                 => cantReify val "Name, reifying it is unimplemented or intentionally internal"
             _ => cantReify val "Name, the name was not found in context"
  reify defs val = cantReify val "Name, value is not an NDCon interally"

export
Reflect UserName where
  reflect fc defs lhs env (Basic x)
      = do x' <- reflect fc defs lhs env x
           appCon fc defs (reflectiontt "Basic") [x']
  reflect fc defs lhs env (Field x)
      = do x' <- reflect fc defs lhs env x
           appCon fc defs (reflectiontt "Field") [x']
  reflect fc defs lhs env Underscore
      = do appCon fc defs (reflectiontt "Underscore") []

export
Reify Name where
  reify defs val@(NDCon _ n _ _ args)
      = case (dropAllNS !(full (gamma defs) n), args) of
             (UN (Basic "UN"), ((_, str) :%: SLNil))
                 => do str' <- reify defs !(evalClosure defs str)
                       pure (UN str')
             (UN (Basic "MN"), ((_, str) :%: (_, i) :%: SLNil))
                 => do str' <- reify defs !(evalClosure defs str)
                       i' <- reify defs !(evalClosure defs i)
                       pure (MN str' i')
             (UN (Basic "NS"), ((_, ns) :%: (_, n) :%: SLNil))
                 => do ns' <- reify defs !(evalClosure defs ns)
                       n' <- reify defs !(evalClosure defs n)
                       pure (NS ns' n')
             (UN (Basic "DN"), ((_, str) :%: (_, n) :%: SLNil))
                 => do str' <- reify defs !(evalClosure defs str)
                       n' <- reify defs !(evalClosure defs n)
                       pure (DN str' n')
             (UN (Basic "Nested"), ((_, ix) :%: (_, n) :%: SLNil))
                 => do ix' <- reify defs !(evalClosure defs ix)
                       n' <- reify defs !(evalClosure defs n)
                       pure (Nested ix' n')
             (UN (Basic "CaseBlock"), ((_, outer) :%: (_, i) :%: SLNil))
                 => do outer' <- reify defs !(evalClosure defs outer)
                       i' <- reify defs !(evalClosure defs i)
                       pure (CaseBlock outer' i')
             (UN (Basic "WithBlock"), ((_, outer) :%: (_, i) :%: SLNil))
                 => do outer' <- reify defs !(evalClosure defs outer)
                       i' <- reify defs !(evalClosure defs i)
                       pure (WithBlock outer' i')
             (NS _ (UN _), _)
                 => cantReify val "Name, reifying it is unimplemented or intentionally internal"
             _ => cantReify val "Name, the name was not found in context"
  reify defs val = cantReify val "Name, value is not an NDCon interally"

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
  reflect fc defs lhs env (Nested ix n)
      = do ix' <- reflect fc defs lhs env ix
           n'  <- reflect fc defs lhs env n
           appCon fc defs (reflectiontt "Nested") [ix',n']
  reflect fc defs lhs env (CaseBlock outer i)
      = do outer' <- reflect fc defs lhs env outer
           i' <- reflect fc defs lhs env i
           appCon fc defs (reflectiontt "CaseBlock") [outer',i']
  reflect fc defs lhs env (WithBlock outer i)
      = do outer' <- reflect fc defs lhs env outer
           i' <- reflect fc defs lhs env i
           appCon fc defs (reflectiontt "WithBlock") [outer',i']
  reflect fc defs lhs env (Resolved i)
      = case !(full (gamma defs) (Resolved i)) of
             Resolved _ => cantReflect fc
                      "Name directly, Resolved is intentionally internal"
             n => reflect fc defs lhs env n
  reflect fc defs lhs env n = cantReflect fc
    "Name, reflecting it is unimplemented or intentionally internal"

export
Reify NameType where
  reify defs val@(NDCon _ n _ _ args)
      = case (dropAllNS !(full (gamma defs) n), args) of
             (UN (Basic "Bound"), _) => pure Bound
             (UN (Basic "Func"), _) => pure Func
             (UN (Basic "DataCon"), ((_, t) :%: (_, i) :%: SLNil))
                  => do t' <- reify defs !(evalClosure defs t)
                        i' <- reify defs !(evalClosure defs i)
                        pure (DataCon t' i')
             (UN (Basic "TyCon"), ((_, t) :%: (_, i) :%: SLNil))
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
Reify PrimType where
  reify defs val@(NDCon _ n _ _ args)
      = case (dropAllNS !(full (gamma defs) n), args) of
             (UN (Basic "IntType"), SLNil)
                  => pure IntType
             (UN (Basic "Int8Type"), SLNil)
                  => pure Int8Type
             (UN (Basic "Int16Type"), SLNil)
                  => pure Int16Type
             (UN (Basic "Int32Type"), SLNil)
                  => pure Int32Type
             (UN (Basic "Int64Type"), SLNil)
                  => pure Int64Type
             (UN (Basic "IntegerType"), SLNil)
                  => pure IntegerType
             (UN (Basic "Bits8Type"), SLNil)
                  => pure Bits8Type
             (UN (Basic "Bits16Type"), SLNil)
                  => pure Bits16Type
             (UN (Basic "Bits32Type"), SLNil)
                  => pure Bits32Type
             (UN (Basic "Bits64Type"), SLNil)
                  => pure Bits64Type
             (UN (Basic "StringType"), SLNil)
                  => pure StringType
             (UN (Basic "CharType"), SLNil)
                  => pure CharType
             (UN (Basic "DoubleType"), SLNil)
                  => pure DoubleType
             (UN (Basic "WorldType"), SLNil)
                  => pure WorldType
             _ => cantReify val "PrimType"
  reify defs val = cantReify val "PrimType"

export
Reify Constant where
  reify defs val@(NDCon _ n _ _ args)
      = case (dropAllNS !(full (gamma defs) n), args) of
             (UN (Basic "I"), ((_, x) :%: SLNil))
                  => do x' <- reify defs !(evalClosure defs x)
                        pure (I x')
             (UN (Basic "I8"), ((_, x) :%: SLNil))
                  => do x' <- reify defs !(evalClosure defs x)
                        pure (I8 x')
             (UN (Basic "I16"), ((_, x) :%: SLNil))
                  => do x' <- reify defs !(evalClosure defs x)
                        pure (I16 x')
             (UN (Basic "I32"), ((_, x) :%: SLNil))
                  => do x' <- reify defs !(evalClosure defs x)
                        pure (I32 x')
             (UN (Basic "I64"), ((_, x) :%: SLNil))
                  => do x' <- reify defs !(evalClosure defs x)
                        pure (I64 x')
             (UN (Basic "BI"), ((_, x) :%: SLNil))
                  => do x' <- reify defs !(evalClosure defs x)
                        pure (BI x')
             (UN (Basic "B8"), ((_, x) :%: SLNil))
                  => do x' <- reify defs !(evalClosure defs x)
                        pure (B8 x')
             (UN (Basic "B16"), ((_, x) :%: SLNil))
                  => do x' <- reify defs !(evalClosure defs x)
                        pure (B16 x')
             (UN (Basic "B32"), ((_, x) :%: SLNil))
                  => do x' <- reify defs !(evalClosure defs x)
                        pure (B32 x')
             (UN (Basic "B64"), ((_, x) :%: SLNil))
                  => do x' <- reify defs !(evalClosure defs x)
                        pure (B64 x')
             (UN (Basic "Str"), ((_, x) :%: SLNil))
                  => do x' <- reify defs !(evalClosure defs x)
                        pure (Str x')
             (UN (Basic "Ch"), ((_, x) :%: SLNil))
                  => do x' <- reify defs !(evalClosure defs x)
                        pure (Ch x')
             (UN (Basic "Db"), ((_, x) :%: SLNil))
                  => do x' <- reify defs !(evalClosure defs x)
                        pure (Db x')
             (UN (Basic "PrT"), ((_, x) :%: SLNil))
                  => do x' <- reify defs !(evalClosure defs x)
                        pure (PrT x')
             (UN (Basic "WorldVal"), SLNil)
                  => pure WorldVal
             _ => cantReify val "Constant"
  reify defs val = cantReify val "Constant"

export
Reflect PrimType where
  reflect fc defs lhs env IntType
      = getCon fc defs (reflectiontt "IntType")
  reflect fc defs lhs env Int8Type
      = getCon fc defs (reflectiontt "Int8Type")
  reflect fc defs lhs env Int16Type
      = getCon fc defs (reflectiontt "Int16Type")
  reflect fc defs lhs env Int32Type
      = getCon fc defs (reflectiontt "Int32Type")
  reflect fc defs lhs env Int64Type
      = getCon fc defs (reflectiontt "Int64Type")
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
Reflect Constant where
  reflect fc defs lhs env (I x)
      = do x' <- reflect fc defs lhs env x
           appCon fc defs (reflectiontt "I") [x']
  reflect fc defs lhs env (I8 x)
      = do x' <- reflect fc defs lhs env x
           appCon fc defs (reflectiontt "I8") [x']
  reflect fc defs lhs env (I16 x)
      = do x' <- reflect fc defs lhs env x
           appCon fc defs (reflectiontt "I16") [x']
  reflect fc defs lhs env (I32 x)
      = do x' <- reflect fc defs lhs env x
           appCon fc defs (reflectiontt "I32") [x']
  reflect fc defs lhs env (I64 x)
      = do x' <- reflect fc defs lhs env x
           appCon fc defs (reflectiontt "I64") [x']
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
  reflect fc defs lhs env (PrT x)
      = do x' <- reflect fc defs lhs env x
           appCon fc defs (reflectiontt "PrT") [x']
  reflect fc defs lhs env WorldVal
      = getCon fc defs (reflectiontt "WorldVal")

export
Reify Visibility where
  reify defs val@(NDCon _ n _ _ _)
      = case dropAllNS !(full (gamma defs) n) of
             UN (Basic "Private") => pure Private
             UN (Basic "Export") => pure Export
             UN (Basic "Public") => pure Public
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
      = case dropAllNS !(full (gamma defs) n) of
             UN (Basic "Total") => pure Total
             UN (Basic "CoveringOnly") => pure CoveringOnly
             UN (Basic "PartialOK") => pure PartialOK
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
      = case dropAllNS !(full (gamma defs) n) of
             UN (Basic "M0") => pure erased
             UN (Basic "M1") => pure linear
             UN (Basic "MW") => pure top
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
      = case (dropAllNS !(full (gamma defs) n), args) of
             (UN (Basic "ImplicitArg"), _) => pure Implicit
             (UN (Basic "ExplicitArg"), _) => pure Explicit
             (UN (Basic "AutoImplicit"), _) => pure AutoImplicit
             (UN (Basic "DefImplicit"), (_ :%: (_, t) :%: SLNil))
                 => do t' <- reify defs !(evalClosure defs t)
                       pure (DefImplicit t')
             _ => cantReify val "PiInfo"
  reify defs val = cantReify val "PiInfo"

export
Reflect t => Reflect (PiInfo t) where
  reflect fc defs lhs env Implicit
      = appCon fc defs (reflectiontt "ImplicitArg") [Erased fc Placeholder]
  reflect fc defs lhs env Explicit
      = appCon fc defs (reflectiontt "ExplicitArg") [Erased fc Placeholder]
  reflect fc defs lhs env AutoImplicit
      = appCon fc defs (reflectiontt "AutoImplicit") [Erased fc Placeholder]
  reflect fc defs lhs env (DefImplicit t)
      = do t' <- reflect fc defs lhs env t
           appCon fc defs (reflectiontt "DefImplicit") [Erased fc Placeholder, t']

export
Reify LazyReason where
  reify defs val@(NDCon _ n _ _ _)
      = case dropAllNS !(full (gamma defs) n) of
             UN (Basic "LInf") => pure LInf
             UN (Basic "LLazy") => pure LLazy
             UN (Basic "LUnknown") => pure LUnknown
             _ => cantReify val "LazyReason"
  reify defs val = cantReify val "LazyReason"

export
Reflect LazyReason where
  reflect fc defs lhs env LInf = getCon fc defs (reflectiontt "LInf")
  reflect fc defs lhs env LLazy = getCon fc defs (reflectiontt "LLazy")
  reflect fc defs lhs env LUnknown = getCon fc defs (reflectiontt "LUnknown")

export
Reify VirtualIdent where
  reify defs val@(NDCon _ n _ _ args)
      = case (dropAllNS !(full (gamma defs) n), args) of
             (UN (Basic "Interactive"), SLNil)
                   => pure Interactive
             _ => cantReify val "VirtualIdent"
  reify defs val = cantReify val "VirtualIdent"

export
Reflect BuiltinType where
  reflect fc defs lhs env BuiltinNatural
      = getCon fc defs (reflectiontt "BuiltinNatural")
  reflect fc defs lhs env NaturalToInteger
      = getCon fc defs (reflectiontt "NaturalToInteger")
  reflect fc defs lhs env IntegerToNatural
      = getCon fc defs (reflectiontt "IntegerToNatural")

export
Reify BuiltinType where
  reify defs val@(NDCon _ n _ _ args)
      = case (dropAllNS !(full (gamma defs) n), args) of
             (UN (Basic "BuiltinNatural"), SLNil)
                   => pure BuiltinNatural
             (UN (Basic "NaturalToInteger"), SLNil)
                   => pure NaturalToInteger
             (UN (Basic "IntegerToNatural"), SLNil)
                   => pure IntegerToNatural
             _ => cantReify val "BuiltinType"
  reify defs val = cantReify val "BuiltinType"

export
Reflect VirtualIdent where
  reflect fc defs lhs env Interactive
      = getCon fc defs (reflectiontt "Interactive")

export
Reify OriginDesc where
  reify defs val@(NDCon _ n _ _ args)
      = case (dropAllNS !(full (gamma defs) n), args) of
             (UN (Basic "PhysicalIdrSrc"), ((_, ident) :%: SLNil))
                   => do ident' <- reify defs !(evalClosure defs ident)
                         pure (PhysicalIdrSrc ident')
             (UN (Basic "PhysicalPkgSrc"), ((_, fname) :%: SLNil))
                   => do fname' <- reify defs !(evalClosure defs fname)
                         pure (PhysicalPkgSrc fname')
             (UN (Basic "Virtual"), ((_, ident) :%: SLNil))
                   => do ident' <- reify defs !(evalClosure defs ident)
                         pure (Virtual ident')
             _ => cantReify val "OriginDesc"
  reify defs val = cantReify val "OriginDesc"

export
Reflect OriginDesc where
  reflect fc defs lhs env (PhysicalIdrSrc ident)
      = do ident' <- reflect fc defs lhs env ident
           appCon fc defs (reflectiontt "PhysicalIdrSrc") [ident']
  reflect fc defs lhs env (PhysicalPkgSrc fname)
      = do fname' <- reflect fc defs lhs env fname
           appCon fc defs (reflectiontt "PhysicalPkgSrc") [fname']
  reflect fc defs lhs env (Virtual ident)
      = do ident' <- reflect fc defs lhs env ident
           appCon fc defs (reflectiontt "Virtual") [ident']

export
Reify FC where
  reify defs val@(NDCon _ n _ _ args)
      = case (dropAllNS !(full (gamma defs) n), args) of
             (UN (Basic "MkFC"), ((_, fn) :%: (_, start) :%: (_, end) :%: SLNil))
                   => do fn' <- reify defs !(evalClosure defs fn)
                         start' <- reify defs !(evalClosure defs start)
                         end' <- reify defs !(evalClosure defs end)
                         pure (MkFC fn' start' end')
             (UN (Basic "EmptyFC"), _) => pure EmptyFC
             _ => cantReify val "FC"
  reify defs val = cantReify val "FC"

export
Reflect FC where
  reflect fc defs True env _ = pure $ Erased fc Placeholder
  reflect fc defs lhs env (MkFC fn start end)
      = do fn' <- reflect fc defs lhs env fn
           start' <- reflect fc defs lhs env start
           end' <- reflect fc defs lhs env end
           appCon fc defs (reflectiontt "MkFC") [fn', start', end']
  reflect fc defs lhs env (MkVirtualFC fn start end)
      = do fn' <- reflect fc defs lhs env fn
           start' <- reflect fc defs lhs env start
           end' <- reflect fc defs lhs env end
           appCon fc defs (reflectiontt "MkFC") [fn', start', end']
  reflect fc defs lhs env EmptyFC = getCon fc defs (reflectiontt "EmptyFC")

export
Reify a => Reify (WithFC a) where
  reify defs val@(NDCon _ n _ _ args)
      = case (dropAllNS !(full (gamma defs) n), map snd args) of
             (UN (Basic "MkFCVal"), [fcterm, nestedVal]) => do
                 fc <- reify defs !(evalClosure defs fcterm)
                 val <- reify defs !(evalClosure defs nestedVal)
                 pure $ MkFCVal fc val
             (UN (Basic "MkFCVal"), [_, fc, l2]) => do
                 fc' <- reify defs !(evalClosure defs fc)
                 val' <- reify defs !(evalClosure defs l2)
                 pure $ MkFCVal fc' val'
             (t, l) => cantReify val "WithFC constructor: \{show t}, args: \{show (length l)}"
  reify defs val = cantReify val "Expected WithFC, found something else"

export
Reflect a => Reflect (WithFC a) where
  reflect fc defs lhs env (MkFCVal loc val)
      = do loc' <- reflect fc defs lhs env loc
           val' <- reflect fc defs lhs env val
           appCon fc defs (reflectiontt "MkFCVal") [Erased fc Placeholder, loc', val']

{-
-- Reflection of well typed terms: We don't reify terms because that involves
-- type checking, but we can reflect them

-- TODO: Do we need this? Fix reify if we do.

export
Reflect (IsVar name idx vs) where
  reflect fc defs lhs env First
      = appCon fc defs (reflectiontt "First") [Erased fc Placeholder, Erased fc Placeholder]
  reflect fc defs lhs env (Later p)
      = do p' <- reflect fc defs lhs env p
           appCon fc defs (reflectiontt "Later")
                  [Erased fc Placeholder, Erased fc Placeholder,
                   Erased fc Placeholder, Erased fc Placeholder, p']

-- Assume terms are normalised so there's not Let bindings in particular
export
Reflect (Term vs) where
  reflect fc defs lhs env (Local {name} lfc _ idx prf)
      = do lfc' <- reflect fc defs lhs env lfc
           idx' <- reflect fc defs lhs env idx
           appCon fc defs (reflectiontt "Local")
                  [Erased fc Placeholder, Erased fc Placeholder, lfc', idx', Erased fc Placeholder]
  reflect fc defs lhs env (Ref rfc nt n)
      = do rfc' <- reflect fc defs lhs env rfc
           nt' <- reflect fc defs lhs env nt
           n' <- reflect fc defs lhs env n
           appCon fc defs (reflectiontt "Ref")
                  [Erased fc Placeholder, rfc', nt', n']
  reflect fc defs lhs env (Bind bfc x (Pi c p ty) sc)
      = do bfc' <- reflect fc defs lhs env bfc
           x' <- reflect fc defs lhs env x
           c' <- reflect fc defs lhs env c
           p' <- reflect fc defs lhs env p
           ty' <- reflect fc defs lhs env ty
           sc' <- reflect fc defs lhs env sc
           appCon fc defs (reflectiontt "Pi")
                  [Erased fc Placeholder, bfc', c', p', x', ty', sc']
  reflect fc defs lhs env (Bind bfc x (Lam c p ty) sc)
      = do bfc' <- reflect fc defs lhs env bfc
           x' <- reflect fc defs lhs env x
           c' <- reflect fc defs lhs env c
           p' <- reflect fc defs lhs env p
           ty' <- reflect fc defs lhs env ty
           sc' <- reflect fc defs lhs env sc
           appCon fc defs (reflectiontt "Lam")
                  [Erased fc Placeholder, bfc', c', p', x', ty', sc']
  reflect fc defs lhs env (App afc fn arg)
      = do afc' <- reflect fc defs lhs env afc
           fn' <- reflect fc defs lhs env fn
           arg' <- reflect fc defs lhs env arg
           appCon fc defs (reflectiontt "App")
                  [Erased fc Placeholder, afc', fn', arg']
  reflect fc defs lhs env (TDelayed dfc r tm)
      = do dfc' <- reflect fc defs lhs env dfc
           r' <- reflect fc defs lhs env r
           tm' <- reflect fc defs lhs env tm
           appCon fc defs (reflectiontt "TDelayed")
                  [Erased fc Placeholder, dfc', r', tm']
  reflect fc defs lhs env (TDelay dfc r ty tm)
      = do dfc' <- reflect fc defs lhs env dfc
           r' <- reflect fc defs lhs env r
           ty' <- reflect fc defs lhs env ty
           tm' <- reflect fc defs lhs env tm
           appCon fc defs (reflectiontt "TDelay")
                  [Erased fc Placeholder, dfc', r', ty', tm']
  reflect fc defs lhs env (TForce dfc r tm)
      = do dfc' <- reflect fc defs lhs env dfc
           r' <- reflect fc defs lhs env r
           tm' <- reflect fc defs lhs env tm
           appCon fc defs (reflectiontt "TForce")
                  [Erased fc Placeholder, r', dfc', tm']
  reflect fc defs lhs env (PrimVal pfc c)
      = do pfc' <- reflect fc defs lhs env pfc
           c' <- reflect fc defs lhs env c
           appCon fc defs (reflectiontt "PrimVal")
                  [Erased fc Placeholder, pfc', c']
  reflect fc defs lhs env (Erased efc _)
      = do efc' <- reflect fc defs lhs env efc
           appCon fc defs (reflectiontt "Erased")
                  [Erased fc Placeholder, efc']
  reflect fc defs lhs env (TType tfc)
      = do tfc' <- reflect fc defs lhs env tfc
           appCon fc defs (reflectiontt "TType")
                  [Erased fc Placeholder, tfc']
  reflect fc defs lhs env val = cantReflect fc "Term"
  -}

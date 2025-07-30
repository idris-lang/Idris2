||| Utilities pertaining to the _lamda-lifted_ intermediate representation of
||| Idris 2 programs.
|||
||| This representation of program syntax is one of several used when compiling
||| a program. These representations can be used by compiler back-ends to
||| compile from versions of Idris programs with reduced complexity---see
||| [Which Intermediate Representation (IR) should be consumed by the custom
||| back-end?]
||| (https://idris2.readthedocs.io/en/latest/backends/backend-cookbook.html?highlight=lifted#which-intermediate-representation-ir-should-be-consumed-by-the-custom-back-end)
||| for more information.
module Compiler.LambdaLift

import Core.CompileExpr
import Core.Context

import Data.String
import Data.Vect
import Data.SnocList.Operations

import Libraries.Data.List.SizeOf
import Libraries.Data.SnocList.SizeOf
import Libraries.Data.SnocList.Extra

%default covering

mutual

  ||| Type representing the syntax tree of an Idris 2 program after lambda
  ||| lifting.
  |||
  ||| All constructors take as argument a file context, describing the position
  ||| of the original code pre-transformation.
  |||
  ||| @ vars is the list of names accessible within the current scope of the
  |||   lambda-lifted code.
  public export
  data Lifted : Scoped where

       ||| A local variable in the lambda-lifted syntax tree.
       |||
       ||| @ idx is the index that the variable can be found at in the syntax
       |||   tree's current scope.
       ||| @ p is evidence that indexing into vars with idx will provide the
       |||   correct variable.
       LLocal : {idx : Nat} -> FC -> (0 p : IsVar x idx vars) -> Lifted vars

       ||| A known function applied to exactly the right number of arguments.
       |||
       ||| Back-end runtimes should be able to utilise total applications
       ||| effectively, and so they are given a specific constructor here.
       |||
       ||| @ lazy is used to signify that this function application is lazy,
       |||   and, if so, the reason for lazy application.
       ||| @ n is the name of the function to be invoked.
       ||| @ args is the list of arguments for the function call.
       LAppName : FC -> (lazy : Maybe LazyReason) -> (n : Name) ->
                  (args : List (Lifted vars)) -> Lifted vars

       ||| A known function applied to fewer arguments than its arity.
       |||
       ||| Situations described by this constructor will likely be handled by
       ||| by runtimes by creating a closure which waits for the remaining
       ||| arguments.
       |||
       ||| @ n is the name of the function to be (eventually) invoked.
       ||| @ missing is the number of arguments missing from this application.
       ||| @ args is a list of the arguments known at this point in time.
       LUnderApp : FC -> (n : Name) -> (missing : Nat) ->
                   (args : List (Lifted vars)) -> Lifted vars

       ||| A closure applied to one more argument.
       |||
       ||| This given argument may be the last one that the closure is waiting
       ||| on before being able to run; runtimes should check for such a
       ||| situation, and run the function if it is now fully applied.
       |||
       ||| @ lazy is used to signify that this function application is lazy,
       |||   and, if so, the reason for lazy application.
       ||| @ closure is the closure being applied.
       ||| @ arg is the extra argument being given to the closure.
       LApp : FC -> (lazy : Maybe LazyReason) -> (closure : Lifted vars) ->
              (arg : Lifted vars) -> Lifted vars

       ||| A let binding: binding a new name to an existing expression.
       |||
       ||| Roughly, this constructor represents code of the form:
       ||| ```idris
       ||| let
       |||   x = expr
       ||| in
       |||   body
       ||| ```
       |||
       ||| @ x is the new name to bind.
       ||| @ expr is the expression to bind `x` to.
       ||| @ body is the expression to evaluate after binding.
       LLet : FC -> (x : Name) -> (expr : Lifted vars) ->
              (body : Lifted (Scope.bind vars x)) -> Lifted vars

       ||| Use of a constructor to construct a compound data type value.
       |||
       ||| @ n is the name of the data type.
       ||| @ info is information about the constructor.
       ||| @ tag is the tag value for the construction, if the type is an
       |||   algebraic data type.
       ||| @ args is the list of arguments for the constructor.
       LCon : FC -> (n : Name) -> (info : ConInfo) -> (tag : Maybe Int) ->
              (args : List (Lifted vars)) -> Lifted vars

       ||| An operator applied to operands.
       |||
       ||| @ arity is the arity of the operator.
       ||| @ lazy is used to signify that this operation is lazy, and, if so,
       |||   the reason for lazy application.
       ||| @ op is the operator being used.
       ||| @ args is a vector containing the operands of the operation.
       LOp : {arity : _} ->
             FC -> (lazy : Maybe LazyReason) -> (op : PrimFn arity) ->
             (args : Vect arity (Lifted vars)) -> Lifted vars

       ||| A second, more involved, form of primitive operation, defined using
       ||| `%extern` pragmas.
       |||
       ||| Backends should cause a compile-time error when encountering an
       ||| unimplemented LExtPrim operation.
       |||
       ||| @ lazy is used to signify that this operation is lazt, and, if so,
       |||   the reason for lazy application.
       ||| @ p is the name of the operator being used.
       ||| @ args is a list of operands for the operation.
       LExtPrim : FC -> (lazy : Maybe LazyReason) -> (p : Name) ->
                  (args : List (Lifted vars)) -> Lifted vars

       ||| A case split on constructor tags.
       |||
       ||| @ expr is the value to match against.
       ||| @ alts is a list of the different branches in the case statement.
       ||| @ def is an (optional) default branch, taken if no branch in alts is
       |||   taken.
       LConCase : FC -> (expr : Lifted vars) ->
                  (alts : List (LiftedConAlt vars)) ->
                  (def : Maybe (Lifted vars)) -> Lifted vars

       ||| A case split on a constant expression.
       |||
       ||| @ expr is the expression to match against.
       ||| @ alts is a list of the different branches in the case statement.
       ||| @ def is an (optional) default branch, taken if no branch in alts is
       |||   taken.
       LConstCase : FC -> (expr : Lifted vars) ->
                    (alts : List (LiftedConstAlt vars)) ->
                    (def : Maybe (Lifted vars)) -> Lifted vars

       ||| A primitive (constant) value.
       LPrimVal : FC -> Constant -> Lifted vars

       ||| An erased value.
       LErased : FC -> Lifted vars

       ||| A forceful crash of the program.
       |||
       ||| This kind of crash is generated by the Idris 2 compiler; it is
       ||| separate from crashes explicitly added to code by programmers (for
       ||| example via `idris_crash`).
       |||
       ||| @ msg is a message emitted when crashing that might be useful for
       |||   debugging.
       LCrash : FC -> (msg : String) -> Lifted vars

  ||| A branch of an "LCon" (constructor tag) case statement.
  |||
  ||| @ vars is the list of names accessible within the current scope of the
  |||   lambda-lifted code.
  public export
  data LiftedConAlt : Scoped where

       ||| Constructs a branch of an "LCon" (constructor tag) case statement.
       |||
       ||| If this branch is taken, members of the compound data value being
       ||| inspected are bound to new names before evaluation continues.
       |||
       ||| @ n is the name of the constructor that this branch checks for.
       ||| @ info is information about the constructor.
       ||| @ tag is a tag value, present if the type of the value
       |||   inspected is an algebraic data type (this can be matched against
       |||   instead of the constructor's name, if preferable).
       ||| @ args is a list of new names that are bound to the inspected value's
       |||   members before evaluation of this branch's body (this is similar
       |||   to using a let binding for each member of the value).
       ||| @ body is the expression that is evaluated as the consequence of
       |||   this branch matching.
       MkLConAlt : (n : Name) -> (info : ConInfo) -> (tag : Maybe Int) ->
                   (args : List Name) -> (body : Lifted (Scope.ext vars args)) ->
                   LiftedConAlt vars

  ||| A branch of an "LConst" (constant expression) case statement.
  |||
  ||| @ vars is the list of names accessible within the current scope of the
  |||   lambda-lifted code.
  public export
  data LiftedConstAlt : Scoped where

       ||| Constructs a branch of an "LConst" (constant expression) case
       ||| statement.
       |||
       ||| @ expr is the constant expression to match against.
       ||| @ body is the expression that is evaluated as the consequence of this
       |||   branch matching.
       MkLConstAlt : (expr : Constant) -> (body : Lifted vars) ->
                     LiftedConstAlt vars

||| Top-level definitions in the lambda-lifted intermediate representation of an
||| Idris 2 program.
public export
data LiftedDef : Type where

     ||| Constructs a function definition.
     |||
     ||| @ args is the arguments accepted by the function.
     ||| @ scope is the list of names accessible within the current scope of the
     |||   lambda-lifted code.
     ||| @ body is the body of the function.
     -- We take the outer scope and the function arguments separately so that
     -- we don't have to reshuffle de Bruijn indices, which is expensive.
     -- This should be compiled as a function which takes 'args' first,
     -- then 'reverse scope'.
     -- (Sorry for the awkward API - it's to do with how the indices are
     -- arranged for the variables, and it could be expensive to reshuffle them!
     -- See Compiler.ANF for an example of how they get resolved to names)
     MkLFun : (args : List Name) -> (scope : Scope) ->
              (body : Lifted (Scope.addInner (cast args) scope)) -> LiftedDef

     ||| Constructs a definition of a constructor for a compound data type.
     |||
     ||| @ tag is a tag value used by the constructor (if present) to keep track
     |||   of the value's type when using algebraic data types.
     ||| @ arity is the arity of the constructor; the number of arguments it
     |||   takes.
     ||| @ nt is information related to newtype unboxing; backend
     |||   implementations needs not make use of this argument, as newtype
     |||   unboxing is managed by the Idris 2 compiler.
     MkLCon : (tag : Maybe Int) -> (arity : Nat) -> (nt : Maybe Nat) ->
              LiftedDef

     ||| Constructs a forward declaration of a foreign function.
     |||
     ||| @ ccs is a list of calling conventions; these are annotations to
     |||   foreign functions, used by backends to relate foreign function calls
     |||   correctly.
     ||| @ fargs is a list of the types of the arguments to the function.
     ||| @ ret is the type of the return value of the function.
     MkLForeign : (ccs : List String) ->
                  (fargs : List CFType) ->
                  (ret : CFType) ->
                  LiftedDef

     ||| Constructs an error condition.
     |||
     ||| The function produced by this construction should accept any number of
     ||| arguments, and should crash at runtime. Such crashes should crash via
     ||| `LCrash` rather than `prim_crash`.
     |||
     ||| @ expl : an explanation of the error.
     MkLError : (expl : Lifted Scope.empty) -> LiftedDef

showLazy : Maybe LazyReason -> String
showLazy = maybe "" $ (" " ++) . show

mutual
  export
  covering
  {vs : _} -> Show (Lifted vs) where
    show (LLocal {idx} _ p) = "!" ++ show (nameAt p)
    show (LAppName fc lazy n args)
        = show n ++ showLazy lazy ++ "(" ++ joinBy ", " (map show args) ++ ")"
    show (LUnderApp fc n m args)
        = "<" ++ show n ++ " underapp " ++ show m ++ ">(" ++
          joinBy ", " (map show args) ++ ")"
    show (LApp fc lazy c arg)
        = show c ++ showLazy lazy ++ " @ (" ++ show arg ++ ")"
    show (LLet fc x val sc)
        = "%let " ++ show x ++ " = " ++ show val ++ " in " ++ show sc
    show (LCon fc n _ t args)
        = "%con " ++ show n ++ "(" ++ joinBy ", " (map show args) ++ ")"
    show (LOp fc lazy op args)
        = "%op " ++ show op ++ showLazy lazy ++ "(" ++ joinBy ", " (toList (map show args)) ++ ")"
    show (LExtPrim fc lazy p args)
        = "%extprim " ++ show p ++ showLazy lazy ++ "(" ++ joinBy ", " (map show args) ++ ")"
    show (LConCase fc sc alts def)
        = "%case " ++ show sc ++ " of { "
             ++ joinBy "| " (map show alts) ++ " " ++ show def
    show (LConstCase fc sc alts def)
        = "%case " ++ show sc ++ " of { "
             ++ joinBy "| " (map show alts) ++ " " ++ show def
    show (LPrimVal _ x) = show x
    show (LErased _) = "___"
    show (LCrash _ x) = "%CRASH(" ++ show x ++ ")"

  export
  covering
  {vs : _} -> Show (LiftedConAlt vs) where
    show (MkLConAlt n _ t args sc)
        = "%conalt " ++ show n ++
             "(" ++ joinBy ", " (map show args) ++ ") => " ++ show sc

  export
  covering
  {vs : _} -> Show (LiftedConstAlt vs) where
    show (MkLConstAlt c sc)
        = "%constalt(" ++ show c ++ ") => " ++ show sc

export
covering
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
         put Lifts ({ nextName := i + 1 } ldefs)
         pure $ mkName (basename ldefs) i
  where
    mkName : Name -> Int -> Name
    mkName (NS ns b) i = NS ns (mkName b i)
    mkName (UN n) i = MN (displayUserName n) i
    mkName (DN _ n) i = mkName n i
    mkName (CaseBlock outer inner) i = MN ("case block in " ++ outer ++ " (" ++ show inner ++ ")") i
    mkName (WithBlock outer inner) i = MN ("with block in " ++ outer ++ " (" ++ show inner ++ ")") i
    mkName n i = MN (show n) i

unload : FC -> (lazy : Maybe LazyReason) -> Lifted vars -> List (Lifted vars) -> Core (Lifted vars)
unload fc _ f [] = pure f
-- only outermost LApp must be lazy as rest will be closures
unload fc lazy f (a :: as) = unload fc Nothing (LApp fc lazy f a) as

record Used (vars : Scope) where
  constructor MkUsed
  used : Vect (length vars) Bool

initUsed : {vars : _} -> Used vars
initUsed {vars} = MkUsed (replicate (length vars) False)

-- TODO upstream
lengthDistributesOverAppend
  : (xs, ys : List a)
  -> length (xs ++ ys) = length xs + length ys
lengthDistributesOverAppend [] ys = Refl
lengthDistributesOverAppend (x :: xs) ys =
  cong S $ lengthDistributesOverAppend xs ys

weakenUsed : {outer : _} -> Used vars -> Used (Scope.addInner vars outer)
weakenUsed {outer} (MkUsed xs) =
  MkUsed (rewrite lengthHomomorphism vars outer in
          rewrite plusCommutative (length vars) (length outer) in
          replicate (length outer) False ++ xs)

weakenUsedFish : {outer : _} -> Used vars -> Used (Scope.ext vars outer)
weakenUsedFish {outer} (MkUsed xs) =
    do rewrite fishAsSnocAppend vars outer
       MkUsed $ do rewrite lengthHomomorphism vars (cast outer)
                   rewrite Extra.lengthDistributesOverFish [<] outer
                   rewrite plusCommutative (length vars) (length outer)
                   replicate (length outer) False ++ xs

contractUsed : (Used (Scope.bind vars x)) -> Used vars
contractUsed (MkUsed xs) = MkUsed (tail xs)

contractUsedMany : {remove : _} ->
                   (Used (Scope.addInner vars remove)) ->
                   Used vars
contractUsedMany {remove=[<]} x = x
contractUsedMany {remove=(rs :< r)} x = contractUsedMany {remove=rs} (contractUsed x)

contractUsedManyFish : {remove : _} ->
                   (Used (vars <>< remove)) ->
                   Used vars
contractUsedManyFish {remove=[]} x = x
contractUsedManyFish {remove=(r :: rs)} x = contractUsed $ contractUsedManyFish {remove=rs} x

markUsed : {vars : _} ->
           (idx : Nat) ->
           {0 prf : IsVar x idx vars} ->
           Used vars ->
           Used vars
markUsed {vars} {prf} idx (MkUsed us) =
  let newUsed = replaceAt (finIdx prf) True us in
  MkUsed newUsed

-- TODO replace ``Vect (length vars) Bool`` by data structure indexed by `vars` so we can erase `vars`
-- TODO this is morally a thinning
getUnused : Used vars ->
            Vect (length vars) Bool
getUnused (MkUsed uv) = map not uv

total
dropped : (vars : Scope) ->
          (drop : Vect (length vars) Bool) ->
          Scope
dropped [<] _ = Scope.empty
dropped (xs :< x) (False::us) = dropped xs us :< x
dropped (xs :< x) (True::us) = dropped xs us

usedVars : {vars : _} ->
           {auto l : Ref Lifts LDefs} ->
           Used vars ->
           Lifted vars ->
           Used vars
usedVars used (LLocal {idx} fc prf) =
  markUsed {prf} idx used
usedVars used (LAppName fc lazy n args) =
  foldl (usedVars {vars}) used args
usedVars used (LUnderApp fc n miss args) =
  foldl (usedVars {vars}) used args
usedVars used (LApp fc lazy c arg) =
  usedVars (usedVars used arg) c
usedVars used (LLet fc x val sc) =
  let innerUsed = contractUsed $ usedVars (weakenUsed {outer=Scope.single x} used) sc in
      usedVars innerUsed val
usedVars used (LCon fc n ci tag args) =
  foldl (usedVars {vars}) used args
usedVars used (LOp fc lazy fn args) =
  foldl (usedVars {vars}) used args
usedVars used (LExtPrim fc lazy fn args) =
  foldl (usedVars {vars}) used args
usedVars used (LConCase fc sc alts def) =
    let defUsed = maybe used (usedVars used {vars}) def
        scDefUsed = usedVars defUsed sc in
        foldl usedConAlt scDefUsed alts
  where
    usedConAlt : {default Nothing lazy : Maybe LazyReason} ->
                  Used vars -> LiftedConAlt vars -> Used vars
    usedConAlt used (MkLConAlt n ci tag args sc) =
      contractUsedManyFish {remove=args} (usedVars (weakenUsedFish used) sc)

usedVars used (LConstCase fc sc alts def) =
    let defUsed = maybe used (usedVars used {vars}) def
        scDefUsed = usedVars defUsed sc in
        foldl usedConstAlt scDefUsed alts
  where
    usedConstAlt : {default Nothing lazy : Maybe LazyReason} ->
                    Used vars -> LiftedConstAlt vars -> Used vars
    usedConstAlt used (MkLConstAlt c sc) = usedVars used sc
usedVars used (LPrimVal _ _) = used
usedVars used (LErased _) = used
usedVars used (LCrash _ _) = used

unsafeDropVar :
  (vars : _) ->
  (unused : Vect (length vars) Bool) ->
  Var vars ->
  Var (dropped vars unused)
unsafeDropVar [<] unused v = v
unsafeDropVar (sx :< x) (False :: us) (MkVar First) = MkVar First
unsafeDropVar (sx :< x) (False :: us) (MkVar (Later idx)) = later $ unsafeDropVar sx us (MkVar idx)
unsafeDropVar (sx :< x) (True :: us) (MkVar First) = assert_total $
  idris_crash "INTERNAL ERROR: Referenced variable marked as unused"
unsafeDropVar (sx :< x) (True :: us) (MkVar (Later idx)) = unsafeDropVar sx us (MkVar idx)


dropIdx : {vars : _} ->
          {idx : _} ->
          SizeOf inner ->
          (unused : Vect (length vars) Bool) ->
          (0 p : IsVar x idx (Scope.addInner vars inner)) ->
          Var (Scope.addInner (dropped vars unused) inner)
dropIdx inn unused p =
  case locateVar inn (MkVar p) of
    Left v => weakenNs inn (unsafeDropVar _ unused v)
    Right v => embed v

-- TODO this is morally a `Shrinkable`. Replace!
0 DropUnused : Scoped -> Type
DropUnused tm =
  {auto _ : Ref Lifts LDefs} ->
  {vars : _} ->
  {0 inner : _}->
  SizeOf inner ->
  (unused : Vect (length vars) Bool) ->
  tm (Scope.addInner vars inner) ->
  tm (Scope.addInner (dropped vars unused) inner)

dropUnused : DropUnused Lifted
dropConCase : DropUnused LiftedConAlt
dropConstCase : DropUnused LiftedConstAlt

dropUnused inn _ (LPrimVal fc val) = LPrimVal fc val
dropUnused inn _ (LErased fc) = LErased fc
dropUnused inn _ (LCrash fc msg) = LCrash fc msg
dropUnused inn unused (LLocal fc p) =
  let (MkVar p') = dropIdx inn unused p in LLocal fc p'
dropUnused inn unused (LCon fc n ci tag args) =
  let args' = map (dropUnused inn unused) args in
      LCon fc n ci tag args'
dropUnused inn unused (LLet fc n val sc) =
  let val' = dropUnused inn unused val
      sc' = dropUnused (suc inn) (unused) sc in
      LLet fc n val' sc'
dropUnused inn unused (LApp fc lazy c arg) =
  let c' = dropUnused inn unused c
      arg' = dropUnused inn unused arg in
      LApp fc lazy c' arg'
dropUnused inn unused (LOp fc lazy fn args) =
  let args' = map (dropUnused inn unused) args in
      LOp fc lazy fn args'
dropUnused inn unused (LExtPrim fc lazy n args) =
  let args' = map (dropUnused inn unused) args in
      LExtPrim fc lazy n args'
dropUnused inn unused (LAppName fc lazy n args) =
  let args' = map (dropUnused inn unused) args in
      LAppName fc lazy n args'
dropUnused inn unused (LUnderApp fc n miss args) =
  let args' = map (dropUnused inn unused) args in
      LUnderApp fc n miss args'
dropUnused inn unused (LConCase fc sc alts def) =
  let alts' = map (dropConCase inn unused) alts in
      LConCase fc (dropUnused inn unused sc) alts' (map (dropUnused inn unused) def)
dropUnused inn unused (LConstCase fc sc alts def) =
  let alts' = map (dropConstCase inn unused) alts in
      LConstCase fc (dropUnused inn unused sc) alts' (map (dropUnused inn unused) def)

dropConCase inn unused (MkLConAlt n ci t args sc) =
  MkLConAlt n ci t args (underBinderz Lifted (\inn => dropUnused inn unused) inn (mkSizeOf args) sc)

dropConstCase inn unused (MkLConstAlt c val) = MkLConstAlt c (dropUnused inn unused val)


mutual
  makeLam : {vars : _} ->
            {auto l : Ref Lifts LDefs} ->
            {doLazyAnnots : Bool} ->
            {default Nothing lazy : Maybe LazyReason} ->
            FC -> (bound : Scope) ->
            CExp (Scope.addInner vars bound) -> Core (Lifted vars)
  makeLam fc bound (CLam _ x sc') = makeLam fc {doLazyAnnots} {lazy} (bound :< x) sc'
  makeLam {vars} fc bound sc
      = do scl <- liftExp {doLazyAnnots} {lazy} sc
           -- Find out which variables aren't used in the new definition, and
           -- do not abstract over them in the new definition.
           let scUsedL = usedVars initUsed scl
               unusedContracted = contractUsedMany {remove=bound} scUsedL
               unused = getUnused unusedContracted
               scl' = dropUnused (mkSizeOf bound) unused scl
           n <- genName
           let scl'' : Lifted ((cast (toList $ dropped vars unused)) ++ bound)
                     := rewrite castToList (dropped vars unused) in scl'
           update Lifts { defs $= ((n, MkLFun (toList $ dropped vars unused) bound scl'') ::) }
           pure $  LUnderApp fc n (length bound) (reverse $ allVars fc vars unused)
    where

        allPrfs : (vs : Scope) -> SizeOf inner -> (unused : Vect (length vs) Bool) -> List (Var (vs <>< inner))
        allPrfs [<] inn _ = []
        allPrfs (vs :< v) inn (False::uvs) = mkVarFishily inn :: allPrfs vs (suc inn) uvs
        allPrfs (vs :< v) inn (True::uvs) = allPrfs vs (suc inn) uvs

        -- apply to all the variables. 'First' will be first in the list, which
        -- is good, because the most recently bound name is the first argument to
        -- the resulting function
        allVars : FC -> (vs : Scope) -> (unused : Vect (length vs) Bool) -> List (Lifted vs)
        allVars fc vs unused = map (\ (MkVar p) => LLocal fc p) (allPrfs vs zero unused)

-- if doLazyAnnots = True then annotate function application with laziness
-- otherwise use old behaviour (thunk is a function)
  liftExp : {vars : _} ->
            {auto l : Ref Lifts LDefs} ->
            {doLazyAnnots : Bool} ->
            {default Nothing lazy : Maybe LazyReason} ->
            CExp vars -> Core (Lifted vars)
  liftExp (CLocal fc prf) = pure $ LLocal fc prf
  liftExp (CRef fc n) = pure $ LAppName fc lazy n [] -- probably shouldn't happen!
  liftExp (CLam fc x sc) = makeLam {doLazyAnnots} {lazy} fc (Scope.single x) sc
  liftExp (CLet fc x _ val sc) = pure $ LLet fc x !(liftExp {doLazyAnnots} val) !(liftExp {doLazyAnnots} sc)
  liftExp (CApp fc (CRef _ n) args) -- names are applied exactly in compileExp
      = pure $ LAppName fc lazy n !(traverse (liftExp {doLazyAnnots}) args)
  liftExp (CApp fc f args)
      = unload fc lazy !(liftExp {doLazyAnnots} f) !(traverse (liftExp {doLazyAnnots}) args)
  liftExp (CCon fc n ci t args) = pure $ LCon fc n ci t !(traverse (liftExp {doLazyAnnots}) args)
  liftExp (COp fc op args)
      = pure $ LOp fc lazy op !(traverseArgs args)
    where
      traverseArgs : Vect n (CExp vars) -> Core (Vect n (Lifted vars))
      traverseArgs [] = pure []
      traverseArgs (a :: as) = pure $ !(liftExp {doLazyAnnots} a) :: !(traverseArgs as)
  liftExp (CExtPrim fc p args) = pure $ LExtPrim fc lazy p !(traverse (liftExp {doLazyAnnots}) args)
  liftExp (CForce fc lazy tm) = if doLazyAnnots
    then liftExp {doLazyAnnots} {lazy = Nothing} tm
    else liftExp {doLazyAnnots} (CApp fc tm [CErased fc])
  liftExp (CDelay fc lazy tm) = if doLazyAnnots
    then liftExp {doLazyAnnots} {lazy = Just lazy} tm
    else liftExp {doLazyAnnots} (CLam fc (MN "act" 0) (weaken tm))
  liftExp (CConCase fc sc alts def)
      = pure $ LConCase fc !(liftExp {doLazyAnnots} sc) !(traverse (liftConAlt {lazy}) alts)
                           !(traverseOpt (liftExp {doLazyAnnots}) def)
    where
      liftConAlt : {default Nothing lazy : Maybe LazyReason} ->
                   CConAlt vars -> Core (LiftedConAlt vars)
      liftConAlt (MkConAlt n ci t args sc) = pure $ MkLConAlt n ci t args !(liftExp {doLazyAnnots} {lazy} sc)
  liftExp (CConstCase fc sc alts def)
      = pure $ LConstCase fc !(liftExp {doLazyAnnots} sc) !(traverse liftConstAlt alts)
                             !(traverseOpt (liftExp {doLazyAnnots}) def)
    where
      liftConstAlt : {default Nothing lazy : Maybe LazyReason} ->
                     CConstAlt vars -> Core (LiftedConstAlt vars)
      liftConstAlt (MkConstAlt c sc) = pure $ MkLConstAlt c !(liftExp {doLazyAnnots} {lazy} sc)
  liftExp (CPrimVal fc c) = pure $ LPrimVal fc c
  liftExp (CErased fc) = pure $ LErased fc
  liftExp (CCrash fc str) = pure $ LCrash fc str

export
liftBody : {vars : _} -> {doLazyAnnots : Bool} ->
           Name -> CExp vars -> Core (Lifted vars, List (Name, LiftedDef))
liftBody n tm
    = do l <- newRef Lifts (MkLDefs n [] 0)
         tml <- liftExp {doLazyAnnots} {l} tm
         ldata <- get Lifts
         pure (tml, defs ldata)

export
lambdaLiftDef : (doLazyAnnots : Bool) -> Name -> CDef -> Core (List (Name, LiftedDef))
lambdaLiftDef doLazyAnnots n (MkFun args exp)
    = do (expl, defs) <- liftBody {doLazyAnnots} n exp
         pure ((n, MkLFun (toList args) Scope.empty (rewrite castToList args in expl)) :: defs)
lambdaLiftDef _ n (MkCon t a nt) = pure [(n, MkLCon t a nt)]
lambdaLiftDef _ n (MkForeign ccs fargs ty) = pure [(n, MkLForeign ccs fargs ty)]
lambdaLiftDef doLazyAnnots n (MkError exp)
    = do (expl, defs) <- liftBody {doLazyAnnots} n exp
         pure ((n, MkLError expl) :: defs)

-- Return the lambda lifted definitions required for the given name.
-- If the name hasn't been compiled yet (via CompileExpr.compileDef) then
-- this will return an empty list
-- An empty list an error, because on success you will always get at least
-- one definition, the lifted definition for the given name.
export
lambdaLift :  (doLazyAnnots : Bool)
           -> (Name,FC,CDef)
           -> Core (List (Name, LiftedDef))
lambdaLift doLazyAnnots (n,_,def) = lambdaLiftDef doLazyAnnots n def

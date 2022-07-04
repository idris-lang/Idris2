||| Deriving functor instances using reflection
||| You can for instance define:
||| ```
||| data Tree a = Leaf a | Node (Tree a) (Tree a)
||| treeFunctor : Functor Tree
||| treeFunctor = %runElab derive
||| ```

module Deriving.Functor

import public Control.Monad.Either
import public Control.Monad.State
import public Data.Maybe
import public Decidable.Equality
import public Language.Reflection

%language ElabReflection
%default total

freshName : List Name -> String -> String
freshName ns a = assert_total $ go (basicNames ns) Nothing where

  basicNames : List Name -> List String
  basicNames = mapMaybe $ \ nm => case dropNS nm of
    UN (Basic str) => Just str
    _ => Nothing

  covering
  go : List String -> Maybe Nat -> String
  go ns mi =
    let nm = a ++ maybe "" show mi in
    ifThenElse (nm `elem` ns) (go ns (Just $ maybe 0 S mi)) nm


------------------------------------------------------------------------------
-- Errors

||| Possible errors for the functor-deriving machinery.
public export
data Error : Type where
  NegativeOccurence : Name -> TTImp -> Error
  NotAnApplication : TTImp -> Error
  NotAFunctor : TTImp -> Error
  NotABifunctor : TTImp -> Error
  NotAFunctorInItsLastArg : TTImp -> Error
  UnsupportedType : TTImp -> Error
  InvalidGoal : Error
  ConfusingReturnType : Error
  -- Contextual information
  WhenCheckingConstructor : Name -> Error -> Error
  WhenCheckingArg : TTImp -> Error -> Error

export
Show Error where
  show = joinBy "\n" . go [<] where

    go : SnocList String -> Error -> List String
    go acc (NegativeOccurence a ty) = acc <>> ["Negative occurence of \{show a} in \{show ty}"]
    go acc (NotAnApplication s) = acc <>> ["The type \{show s} is not an application"]
    go acc (NotAFunctor s) = acc <>> ["Couldn't find a `Functor' instance for the type constructor \{show s}"]
    go acc (NotABifunctor s) = acc <>> ["Couldn't find a `Bifunctor' instance for the type constructor \{show s}"]
    go acc (NotAFunctorInItsLastArg s) = acc <>> ["Not a functor in its last argument \{show s}"]
    go acc (UnsupportedType s) = acc <>> ["Unsupported type \{show s}"]
    go acc InvalidGoal = acc <>> ["Expected a goal of the form `Functor f`"]
    go acc ConfusingReturnType = acc <>> ["Confusing telescope"]
    go acc (WhenCheckingConstructor nm err) = go (acc :< "When checking constructor \{show nm}") err
    go acc (WhenCheckingArg s err) = go (acc :< "When checking argument of type \{show s}") err

------------------------------------------------------------------------------
-- Preliminaries: satisfying an interface
--
-- In order to derive Functor for `data Tree a = Node (List (Tree a))`, we need
-- to make sure that `Functor List` already exists. This is done using the following
-- convenience functions.

record IsType where
  constructor MkIsType
  typeConstructor  : Name
  parameterNames   : List (Name, Nat)
  dataConstructors : List (Name, TTImp)

wording : NameType -> String
wording Bound = "a bound variable"
wording Func = "a function name"
wording (DataCon tag arity) = "a data constructor"
wording (TyCon tag arity) = "a type constructor"

isTypeCon : Elaboration m => Name -> m (List (Name, TTImp))
isTypeCon ty = do
    [(_, MkNameInfo (TyCon _ _))] <- getInfo ty
      | [] => fail "\{show ty} out of scope"
      | [(_, MkNameInfo nt)] => fail "\{show ty} is \{wording nt} rather than a type constructor"
      | _ => fail "\{show ty} is ambiguous"
    cs <- getCons ty
    for cs $ \ n => do
      [(_, ty)] <- getType n
         | _ => fail "\{show n} is ambiguous"
      pure (n, ty)

isType : Elaboration m => TTImp -> m IsType
isType = go Z where

  go : Nat -> TTImp -> m IsType
  go idx (IVar _ n) = MkIsType n [] <$> isTypeCon n
  go idx (IApp _ t (IVar _ nm)) = case nm of
    -- Unqualified: that's a local variable
    UN (Basic _) => { parameterNames $= ((nm, idx) ::) } <$> go (S idx) t
    _ => go (S idx) t
  go idx t = fail "Expected a type constructor, got: \{show t}"

record Parameters where
  constructor MkParameters
  asFunctors : List Nat
  asBifunctors : List Nat

initParameters : Parameters
initParameters = MkParameters [] []

withParams : FC -> Parameters -> List (Name, Nat) -> TTImp -> TTImp
withParams fc params nms t = go nms where

  addConstraint : Bool -> Name -> Name -> TTImp -> TTImp
  addConstraint False _ _ = id
  addConstraint True cst nm =
     let ty = IApp fc (IVar fc cst) (IVar fc nm) in
     IPi fc MW AutoImplicit Nothing ty

  go : List (Name, Nat) -> TTImp
  go [] = t
  go ((nm, pos) :: nms)
    = IPi fc M0 ImplicitArg (Just nm) (Implicit fc True)
    $ addConstraint (pos `elem` params.asFunctors)   `{Prelude.Interfaces.Functor}   nm
    $ addConstraint (pos `elem` params.asBifunctors) `{Prelude.Interfaces.Bifunctor} nm
    $ go nms

||| Type of proofs that a type satisfies a constraint.
||| Internally it's vacuous. We don't export the constructor so
||| that users cannot manufacture buggy proofs.
export
data HasImplementation : (intf : a -> Type) -> TTImp -> Type where
  TrustMeHI : HasImplementation intf t

||| Given
||| @ intf an interface (e.g. `Functor`, or `Bifunctor`)
||| @ t    a term corresponding to a (possibly partially applied) type constructor
||| check whether Idris2 can find a proof that t satisfies the interface.
export
hasImplementation : Elaboration m => (intf : a -> Type) -> (t : TTImp) ->
                    m (Maybe (HasImplementation intf t))
hasImplementation c t = catch $ do
  prf <- isType t
  intf <- quote c
  ty <- check {expected = Type} $ withParams emptyFC initParameters prf.parameterNames `(~(intf) ~(t))
  ignore $ check {expected = ty} `(%search)
  pure TrustMeHI

------------------------------------------------------------------------------
-- Core machinery: being functorial

||| IsFunctorialIn is parametrised by
||| @ t  the name of the data type whose constructors are being analysed
||| @ x  the name of the type variable that the functioral action will change
||| @ ty the type being analysed
||| The inductive type delivers a proof that x occurs positively in ty,
||| assuming that t also is positive.
public export
data IsFunctorialIn : (t, x : Name) -> (ty : TTImp) -> Type

||| FreeOf is parametrised by
||| @ x  the name of the type variable that the functioral action will change
||| @ ty the type that does not contain any mention of x
export
data FreeOf : (x : Name) -> (ty : TTImp) -> Type

data IsFunctorialIn : (t, x : Name) -> TTImp -> Type where
  ||| The type variable x occurs alone
  FIVar : IsFunctorialIn t x (IVar fc x)
  ||| There is a recursive subtree of type (t a1 ... an u) and u is functorial in x.
  ||| We do not insist that u is exactly x so that we can deal with nested types
  ||| like the following:
  |||   data Full a = Leaf a | Node (Full (a, a))
  |||   data Term a = Var a | App (Term a) (Term a) | Lam (Term (Maybe a))
  FIRec : (0 _ : IsAppView (_, t) _ f) -> IsFunctorialIn t x arg -> IsFunctorialIn t x (IApp fc f arg)
  ||| The subterm is delayed (either Inf or Lazy)
  FIDelayed : IsFunctorialIn t x ty -> IsFunctorialIn t x (IDelayed fc lr ty)
  ||| There are nested subtrees somewhere inside a 3rd party type constructor
  ||| which satisfies the Bifunctor interface
  FIBifun : HasImplementation Bifunctor sp ->
            IsFunctorialIn t x arg1 -> Either (IsFunctorialIn t x arg2) (FreeOf x arg2) ->
            IsFunctorialIn t x (IApp fc1 (IApp fc2 sp arg1) arg2)
  ||| There are nested subtrees somewhere inside a 3rd party type constructor
  ||| which satisfies the Functor interface
  FIFun : HasImplementation Functor sp ->
          IsFunctorialIn t x arg -> IsFunctorialIn t x (IApp fc sp arg)
  ||| A pi type, with no negative occurence of x in its domain
  FIPi : FreeOf x a -> IsFunctorialIn t x b -> IsFunctorialIn t x (IPi fc rig pinfo nm a b)
  ||| A type free of x is trivially Functorial in it
  FIFree : FreeOf x a -> IsFunctorialIn t x a

data FreeOf : Name -> TTImp -> Type where
  ||| For now we do not bother keeping precise track of the proof that a type
  ||| is free of x
  TrustMeFO : FreeOf a x

elemPos : Eq a => a -> List a -> Maybe Nat
elemPos x = go 0 where

  go : Nat -> List a -> Maybe Nat
  go idx [] = Nothing
  go idx (y :: ys) = idx <$ guard (x == y) <|> go (S idx) ys

parameters
  {0 m : Type -> Type}
  {auto elab : Elaboration m}
  {auto error : MonadError Error m}
  {auto cs : MonadState Parameters m}
  (t : Name)
  (ps : List Name)
  (x : Name)

  ||| When analysing the type of a constructor for the type family t,
  ||| we hope to observe
  |||   1. either that it is functorial in x
  |||   2. or that it is free of x
  ||| If if it is not the case, we will use the `MonadError Error` constraint
  ||| to fail with an informative message.
  public export
  TypeView : TTImp -> Type
  TypeView ty = Either (IsFunctorialIn t x ty) (FreeOf x ty)

  ||| Hoping to observe that ty is functorial
  export
  typeView : (ty : TTImp) -> m (TypeView ty)

  ||| To avoid code duplication in typeView, we have an auxiliary function
  ||| specifically to handle the application case
  typeAppView : {fc : FC} -> (f, arg : TTImp) -> m (TypeView (IApp fc f arg))

  typeAppView {fc} f arg = do
    chka <- typeView arg
    case chka of
      -- if x is present in the argument then the function better be:
      -- 1. either an occurrence of t i.e. a subterm
      -- 2. or a type constructor already known to be functorial
      Left sp => do
        let Just (MkAppView (_, hd) ts prf) = appView f
           | _ => throwError (NotAnApplication f)
        case decEq t hd of
          Yes Refl => pure $ Left (FIRec prf sp)
          No diff => case !(hasImplementation Functor f) of
            Just prf => pure (Left (FIFun prf sp))
            Nothing => case hd `elemPos` ps of
              Just n => do
                -- record that the nth parameter should be functorial
                ns <- gets asFunctors
                let ns = ifThenElse (n `elem` ns) ns (n :: ns)
                modify { asFunctors := ns }
                -- and happily succeed
                logMsg "derive.functor.assumption" 10 $
                  "I am assuming that the parameter \{show hd} is a Functor"
                pure (Left (FIFun TrustMeHI sp))
              Nothing => throwError (NotAFunctor f)
      -- Otherwise it better be the case that f is also free of x so that
      -- we can mark the whole type as being x-free.
      Right fo => do
        Right _ <- typeView f
          | _ => throwError (NotAFunctorInItsLastArg (IApp fc f arg))
        pure (Right TrustMeFO)

  typeView (IVar fc y) = pure $ case decEq x y of
    Yes Refl => Left FIVar
    No _ => Right TrustMeFO
  typeView ty@(IPi fc rig pinfo nm a b) = do
    Right p <- typeView a
      | _ => throwError (NegativeOccurence x ty)
    Left q <- typeView b
      | _ => pure (Right TrustMeFO)
    pure (Left (FIPi p q))
  typeView fa@(IApp _ (IApp _ f arg1) arg2) = do
    chka1 <- typeView arg1
    case chka1 of
      Right _ => typeAppView (assert_smaller fa (IApp _ f arg1)) arg2
      Left sp => case !(hasImplementation Bifunctor f) of
        Just prf => pure (Left (FIBifun prf sp !(typeView arg2)))
        Nothing => do
          let Just (MkAppView (_, hd) ts prf) = appView f
             | _ => throwError (NotAnApplication f)
          case hd `elemPos` ps of
            Just n => do
              -- record that the nth parameter should be bifunctorial
              ns <- gets asBifunctors
              let ns = ifThenElse (n `elem` ns) ns (n :: ns)
              modify { asBifunctors := ns }
              -- and happily succeed
              logMsg "derive.functor.assumption" 10 $
                  "I am assuming that the parameter \{show hd} is a Bifunctor"
              pure (Left (FIBifun TrustMeHI sp !(typeView arg2)))
            Nothing => throwError (NotABifunctor f)
  typeView fa@(IApp _ f arg) = typeAppView f arg
  typeView (IDelayed _ lz f) = pure $ case !(typeView f) of
    Left sp => Left (FIDelayed sp)
    Right _ => Right TrustMeFO
  typeView (IPrimVal _ _) = pure (Right TrustMeFO)
  typeView (IType _) = pure (Right TrustMeFO)
  typeView ty = throwError (UnsupportedType ty)

------------------------------------------------------------------------------
-- Core machinery: building the mapping function from an IsFunctorialIn proof

||| We often apply multiple arguments, this makes things simpler
apply : FC -> TTImp -> List TTImp -> TTImp
apply fc = foldl (IApp fc)

parameters (fc : FC) (mutualWith : List Name)

  ||| functorFun takes
  ||| @ mutualWith a list of mutually defined type constructors. Calls to their
  ||| respective mapping functions typically need an assert_total because the
  ||| termination checker is not doing enough inlining to see that things are
  ||| terminating
  ||| @ assert records whether we should mark recursive calls as total because
  ||| we are currently constructing the argument to a higher order function
  ||| which will obscure the termination argument. Starts as `Nothing`, becomes
  ||| `Just False` if an `assert_total` has already been inserted.
  ||| @ ty the type being transformed by the mapping function
  ||| @ rec the name of the mapping function being defined (used for recursive calls)
  ||| @ f the name of the function we're mapping
  ||| @ arg the (optional) name of the argument being mapped over. This lets us use
  ||| Nothing when generating arguments to higher order functions so that we generate
  ||| the eta contracted `map (mapTree f)` instead of `map (\ ts => mapTree f ts)`.
  functorFun : (assert : Maybe Bool) -> {ty : TTImp} -> IsFunctorialIn t x ty ->
               (rec, f : Name) -> (arg : Maybe TTImp) -> TTImp
  functorFun assert FIVar rec f t = apply fc (IVar fc f) (toList t)
  functorFun assert (FIRec y sp) rec f t
    -- only add assert_total if it is declared to be needed
    = ifThenElse (fromMaybe False assert) (IApp fc (IVar fc (UN $ Basic "assert_total"))) id
    $ apply fc (IVar fc rec) (functorFun (Just False) sp rec f Nothing :: toList t)
  functorFun assert (FIDelayed sp) rec f Nothing
    -- here we need to eta-expand to avoid "Lazy t does not unify with t" errors
    = let nm = UN $ Basic "eta" in
      ILam fc MW ExplicitArg (Just nm) (Implicit fc False)
    $ IDelay fc
    $ functorFun assert sp rec f (Just (IVar fc nm))
  functorFun assert (FIDelayed sp) rec f (Just t) = functorFun assert sp rec f (Just t)
  functorFun assert {ty = IApp _ ty _} (FIFun _ sp) rec f t
    -- only add assert_total if we are calling a mutually defined Functor implementation.
    = let isMutual = fromMaybe False (appView ty >>= \ v => pure (snd v.head `elem` mutualWith)) in
      ifThenElse isMutual (IApp fc (IVar fc (UN $ Basic "assert_total"))) id
    $ apply fc (IVar fc (UN $ Basic "map"))
      (functorFun ((False <$ guard isMutual) <|> assert <|> Just True) sp rec f Nothing
       :: toList t)
  functorFun assert (FIBifun _ sp1 (Left sp2)) rec f t
    = apply fc (IVar fc (UN $ Basic "bimap"))
      (functorFun (assert <|> Just True) sp1 rec f Nothing
      :: functorFun (assert <|> Just True) sp2 rec f Nothing
      :: toList t)
  functorFun assert (FIBifun _ sp (Right _)) rec f t
    = apply fc (IVar fc (UN $ Basic "mapFst"))
      (functorFun (assert <|> Just True) sp rec f Nothing
      :: toList t)
  functorFun assert (FIPi {rig, pinfo, nm} _ sp) rec f (Just t)
    = let nm = fromMaybe (UN $ Basic "x") nm in
      -- /!\ We cannot use the type stored in FIPi here because it could just
      -- be a name that will happen to be different when bound on the LHS!
      -- Cf. the Free test case in reflection017
      ILam fc rig pinfo (Just nm) (Implicit fc False)
    $ functorFun assert sp rec f (Just $ IApp fc t (IVar fc nm))
  functorFun assert (FIPi {rig, pinfo, nm} _ sp) rec f Nothing
    = let tnm = UN $ Basic "t" in
      let nm = fromMaybe (UN $ Basic "x") nm in
      ILam fc MW ExplicitArg (Just tnm) (Implicit fc False) $
      -- /!\ We cannot use the type stored in FIPi here because it could just
      -- be a name that will happen to be different when bound on the LHS!
      -- Cf. the Free test case in reflection017
      ILam fc rig pinfo (Just nm) (Implicit fc False) $
      functorFun assert sp rec f (Just $ IApp fc (IVar fc tnm) (IVar fc nm))
  functorFun assert (FIFree y) rec f t = fromMaybe `(id) t

------------------------------------------------------------------------------
-- User-facing: Functor deriving

record ConstructorView where
  constructor MkConstructorView
  params      : List Name
  functorPara : Name
  conArgTypes : List TTImp

explicits : TTImp -> Maybe ConstructorView
explicits (IPi fc rig ExplicitArg x a b) = { conArgTypes $= (a ::) } <$> explicits b
explicits (IPi fc rig pinfo x a b) = explicits b
explicits (IApp _ f (IVar _ a)) = do
  MkAppView _ ts _ <- appView f
  let ps = flip mapMaybe ts $ \ t => the (Maybe Name) $ case t of
             Arg _ (IVar _ nm) => Just nm
             _ => Nothing
  pure (MkConstructorView (ps <>> []) a [])
explicits _ = Nothing

cleanup : TTImp -> TTImp
cleanup = \case
  IVar fc n => IVar fc (dropNS n)
  t => t

namespace Functor

  derive' : (Elaboration m, MonadError Error m) =>
            {default Private vis : Visibility} ->
            {default Total treq : TotalReq} ->
            {default [] mutualWith : List Name} ->
            m (Functor f)
  derive' = do

    -- expand the mutualwith names to have the internal, fully qualified, names
    mutualWith <- map concat $ for mutualWith $ \ nm => do
                    ntys <- getType nm
                    pure (fst <$> ntys)

    -- The goal should have the shape (Functor t)
    Just (IApp _ (IVar _ functor) t) <- goal
      | _ => throwError InvalidGoal
    when (`{Prelude.Interfaces.Functor} /= functor) $
      logMsg "derive.functor" 1 "Expected to derive Functor but got \{show functor}"

    -- t should be a type constructor
    logMsg "derive.functor" 1 "Deriving Functor for \{showPrec App $ mapTTImp cleanup t}"
    MkIsType f params cs <- isType t
    logMsg "derive.functor.constructors" 1 $
      joinBy "\n" $ "" :: map (\ (n, ty) => "  \{showPrefix True $ dropNS n} : \{show $ mapTTImp cleanup ty}") cs

    -- Generate a clause for each data constructor
    let fc = emptyFC
    let un = UN . Basic
    let mapName = un ("map" ++ show (dropNS f))
    let funName = un "f"
    let fun  = IVar fc funName
    (ns, cls) <- runStateT {m = m} initParameters $ for cs $ \ (cName, ty) =>
      withError (WhenCheckingConstructor cName) $ do
        -- Grab the types of the constructor's explicit arguments
        let Just (MkConstructorView paras para args) = explicits ty
              | _ => throwError ConfusingReturnType
        logMsg "derive.functor.clauses" 10 $
          "\{showPrefix True (dropNS cName)} (\{joinBy ", " (map (showPrec Dollar . mapTTImp cleanup) args)})"
        let vars = map (IVar fc . un . ("x" ++) . show . (`minus` 1))
                 $ zipWith const [1..length args] args -- fix because [1..0] is [1,0]
        recs <- for (zip vars args) $ \ (v, arg) => do
                  res <- withError (WhenCheckingArg (mapTTImp cleanup arg)) $
                           typeView f paras para arg
                  pure $ case res of
                    Left sp => -- do not bother with assert_total if you're generating
                               -- a covering/partial definition
                               let useTot = False <$ guard (treq /= Total) in
                               functorFun fc mutualWith useTot sp mapName funName (Just v)
                    Right free => v
        pure $ PatClause fc
          (apply fc (IVar fc mapName) [ fun, apply fc (IVar fc cName) vars])
          (apply fc (IVar fc cName) recs)

    -- Generate the type of the mapping function
    let paramNames = fst <$> params
    let a = un $ freshName paramNames "a"
    let b = un $ freshName paramNames "b"
    let va = IVar fc a
    let vb = IVar fc b
    let ty = MkTy fc fc mapName $ withParams fc ns params
           $ IPi fc M0 ImplicitArg (Just a) (IType fc)
           $ IPi fc M0 ImplicitArg (Just b) (IType fc)
           $ `((~(va) -> ~(vb)) -> ~(t) ~(va) -> ~(t) ~(vb))
    logMsg "derive.functor.clauses" 1 $
      joinBy "\n" ("" :: ("  " ++ show (mapITy cleanup ty))
                      :: map (("  " ++) . showClause InDecl . mapClause cleanup) cls)

    -- Define the instance
    check $ ILocal fc
      [ IClaim fc MW vis [Totality treq] ty
      , IDef fc mapName cls
      ] `(MkFunctor {f = ~(t)} ~(IVar fc mapName))

  ||| Derive an implementation of Functor for a type constructor.
  ||| This can be used like so:
  ||| ```
  ||| data Tree a = Leaf a | Node (Tree a) (Tree a)
  ||| treeFunctor : Functor Tree
  ||| treeFunctor = %runElab derive
  ||| ```
  export
  derive : {default Private vis : Visibility} ->
           {default Total treq : TotalReq} ->
           {default [] mutualWith : List Name} ->
           Elab (Functor f)
  derive = do
    res <- runEitherT {e = Error, m = Elab} (derive' {vis, treq, mutualWith})
    case res of
      Left err => fail (show err)
      Right prf => pure prf

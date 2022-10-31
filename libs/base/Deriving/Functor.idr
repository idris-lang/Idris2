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

import public Deriving.Common

%language ElabReflection
%default total

------------------------------------------------------------------------------
-- Errors

||| Possible errors for the functor-deriving machinery.
public export
data Error : Type where
  NotFreeOf : Name -> TTImp -> Error
  NegativeOccurrence : Name -> TTImp -> Error
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
    go acc (NotFreeOf x ty) = acc <>> ["The term \{show ty} is not free of \{show x}"]
    go acc (NegativeOccurrence a ty) = acc <>> ["Negative occurrence of \{show a} in \{show ty}"]
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
-- Core machinery: being functorial

-- Not meant to be re-exported as it's using the internal notion of error
isFreeOf' :
  {0 m : Type -> Type} ->
  {auto elab : Elaboration m} ->
  {auto error : MonadError Error m} ->
  (x : Name) -> (ty : TTImp) -> m (IsFreeOf x ty)
isFreeOf' x ty = case isFreeOf x ty of
  Nothing => throwError (NotFreeOf x ty)
  Just prf => pure prf

public export
data Polarity = Positive | Negative

public export
not : Polarity -> Polarity
not Positive = Negative
not Negative = Positive

||| IsFunctorialIn is parametrised by
||| @ pol the polarity of the type being analysed. We start in positive polarity
|||       where occurrences of x are allowed and negate the polarity every time
|||       we step into the domain of a Pi type.
||| @ t  the name of the data type whose constructors are being analysed
||| @ x  the name of the type variable that the functioral action will change
||| @ ty the type being analysed
||| The inductive type delivers a proof that x occurs positively in ty,
||| assuming that t also is positive.
public export
data IsFunctorialIn : (pol : Polarity) -> (t, x : Name) -> (ty : TTImp) -> Type where
  ||| The type variable x occurs alone
  FIVar : IsFunctorialIn Positive t x (IVar fc x)
  ||| There is a recursive subtree of type (t a1 ... an u) and u is functorial in x.
  ||| We do not insist that u is exactly x so that we can deal with nested types
  ||| like the following:
  |||   data Full a = Leaf a | Node (Full (a, a))
  |||   data Term a = Var a | App (Term a) (Term a) | Lam (Term (Maybe a))
  FIRec : (0 _ : IsAppView (_, t) _ f) -> IsFunctorialIn pol t x arg ->
          IsFunctorialIn Positive t x (IApp fc f arg)
  ||| The subterm is delayed (either Inf or Lazy)
  FIDelayed : IsFunctorialIn pol t x ty -> IsFunctorialIn pol t x (IDelayed fc lr ty)
  ||| There are nested subtrees somewhere inside a 3rd party type constructor
  ||| which satisfies the Bifunctor interface
  FIBifun : IsFreeOf x sp -> HasImplementation Bifunctor sp ->
            IsFunctorialIn pol t x arg1 -> Either (IsFunctorialIn pol t x arg2) (IsFreeOf x arg2) ->
            IsFunctorialIn pol t x (IApp fc1 (IApp fc2 sp arg1) arg2)
  ||| There are nested subtrees somewhere inside a 3rd party type constructor
  ||| which satisfies the Functor interface
  FIFun : IsFreeOf x sp -> HasImplementation Functor sp ->
          IsFunctorialIn pol t x arg -> IsFunctorialIn pol t x (IApp fc sp arg)
  ||| A pi type, with no negative occurrence of x in its domain
  FIPi : IsFunctorialIn (not pol) t x a -> IsFunctorialIn pol t x b ->
         IsFunctorialIn pol t x (IPi fc rig pinfo nm a b)
  ||| A type free of x is trivially Functorial in it
  FIFree : IsFreeOf x a -> IsFunctorialIn pol t x a

record Parameters where
  constructor MkParameters
  asFunctors : List Nat
  asBifunctors : List Nat

initParameters : Parameters
initParameters = MkParameters [] []

paramConstraints : Parameters -> Nat -> Maybe TTImp
paramConstraints params pos
    = IVar emptyFC `{Prelude.Interfaces.Functor}   <$ guard (pos `elem` params.asFunctors)
  <|> IVar emptyFC `{Prelude.Interfaces.Bifunctor} <$ guard (pos `elem` params.asBifunctors)

parameters
  {0 m : Type -> Type}
  {auto elab : Elaboration m}
  {auto error : MonadError Error m}
  {auto cs : MonadState Parameters m}
  (t : Name)
  (ps : List (Name, Nat))
  (x : Name)

  ||| When analysing the type of a constructor for the type family t,
  ||| we hope to observe
  |||   1. either that it is functorial in x
  |||   2. or that it is free of x
  ||| If if it is not the case, we will use the `MonadError Error` constraint
  ||| to fail with an informative message.
  public export
  TypeView : Polarity -> TTImp -> Type
  TypeView pol ty = Either (IsFunctorialIn pol t x ty) (IsFreeOf x ty)

  export
  fromTypeView : TypeView pol ty -> IsFunctorialIn pol t x ty
  fromTypeView (Left prf) = prf
  fromTypeView (Right fo) = FIFree fo

  ||| Hoping to observe that ty is functorial
  export
  typeView : {pol : Polarity} -> (ty : TTImp) -> m (TypeView pol ty)

  ||| To avoid code duplication in typeView, we have an auxiliary function
  ||| specifically to handle the application case
  typeAppView :
    {fc : FC} -> {pol : Polarity} ->
    {f : TTImp} -> IsFreeOf x f ->
    (arg : TTImp) ->
    m (TypeView pol (IApp fc f arg))

  typeAppView {fc, pol, f} isFO arg = do
    chka <- typeView arg
    case chka of
      -- if x is present in the argument then the function better be:
      -- 1. free of x
      -- 2. either an occurrence of t i.e. a subterm
      --    or a type constructor already known to be functorial
      Left sp => do
        let Just (MkAppView (_, hd) ts prf) = appView f
           | _ => throwError (NotAnApplication f)
        case decEq t hd of
          Yes Refl => case pol of
            Positive => pure $ Left (FIRec prf sp)
            Negative => throwError (NegativeOccurrence t (IApp fc f arg))
          No diff => case !(hasImplementation Functor f) of
            Just prf => pure (Left (FIFun isFO prf sp))
            Nothing => case lookup hd ps of
              Just n => do
                -- record that the nth parameter should be functorial
                ns <- gets asFunctors
                let ns = ifThenElse (n `elem` ns) ns (n :: ns)
                modify { asFunctors := ns }
                -- and happily succeed
                logMsg "derive.functor.assumption" 10 $
                  "I am assuming that the parameter \{show hd} is a Functor"
                pure (Left (FIFun isFO assert_hasImplementation sp))
              Nothing => throwError (NotAFunctor f)
      -- Otherwise it better be the case that f is also free of x so that
      -- we can mark the whole type as being x-free.
      Right fo => do
        Right _ <- typeView {pol} f
          | _ => throwError $ case pol of
                   Positive => NotAFunctorInItsLastArg (IApp fc f arg)
                   Negative => NegativeOccurrence x (IApp fc f arg)
        pure (Right assert_IsFreeOf)

  typeView {pol} tm@(IVar fc y) = case decEq x y of
    Yes Refl => case pol of
      Positive => pure (Left FIVar)
      Negative => throwError (NegativeOccurrence x tm)
    No _ => pure (Right assert_IsFreeOf)
  typeView ty@(IPi fc rig pinfo nm a b) = do
    va <- typeView a
    vb <- typeView b
    pure $ case (va, vb) of
      (_, Left sp) => Left (FIPi (fromTypeView va) sp)
      (Left sp,  _) => Left (FIPi sp (fromTypeView vb))
      (Right _, Right _) => Right assert_IsFreeOf
  typeView fab@(IApp _ (IApp fc1 f arg1) arg2) = do
    chka1 <- typeView arg1
    case chka1 of
      Right _ => do isFO <- isFreeOf' x (IApp _ f arg1)
                    typeAppView {f = assert_smaller fab (IApp _ f arg1)} isFO arg2
      Left sp => do
        isFO <- isFreeOf' x f
        case !(hasImplementation Bifunctor f) of
          Just prf => pure (Left (FIBifun isFO prf sp !(typeView arg2)))
          Nothing => do
            let Just (MkAppView (_, hd) ts prf) = appView f
               | _ => throwError (NotAnApplication f)
            case lookup hd ps of
              Just n => do
                -- record that the nth parameter should be bifunctorial
                ns <- gets asBifunctors
                let ns = ifThenElse (n `elem` ns) ns (n :: ns)
                modify { asBifunctors := ns }
                -- and happily succeed
                logMsg "derive.functor.assumption" 10 $
                    "I am assuming that the parameter \{show hd} is a Bifunctor"
                pure (Left (FIBifun isFO assert_hasImplementation sp !(typeView arg2)))
              Nothing => throwError (NotABifunctor f)
  typeView (IApp _ f arg) = do
    isFO <- isFreeOf' x f
    typeAppView isFO arg
  typeView (IDelayed _ lz f) = pure $ case !(typeView f) of
    Left sp => Left (FIDelayed sp)
    Right _ => Right assert_IsFreeOf
  typeView (IPrimVal _ _) = pure (Right assert_IsFreeOf)
  typeView (IType _) = pure (Right assert_IsFreeOf)
  typeView ty = throwError (UnsupportedType ty)

------------------------------------------------------------------------------
-- Core machinery: building the mapping function from an IsFunctorialIn proof

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
  functorFun : (assert : Maybe Bool) -> {ty : TTImp} -> IsFunctorialIn pol t x ty ->
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
  functorFun assert (FIDelayed sp) rec f (Just t)
    = IDelay fc
    $ functorFun assert sp rec f (Just t)
  functorFun assert {ty = IApp _ ty _} (FIFun _ _ sp) rec f t
    -- only add assert_total if we are calling a mutually defined Functor implementation.
    = let isMutual = fromMaybe False (appView ty >>= \ v => pure (snd v.head `elem` mutualWith)) in
      ifThenElse isMutual (IApp fc (IVar fc (UN $ Basic "assert_total"))) id
    $ apply fc (IVar fc (UN $ Basic "map"))
      (functorFun ((False <$ guard isMutual) <|> assert <|> Just True) sp rec f Nothing
       :: toList t)
  functorFun assert (FIBifun _ _ sp1 (Left sp2)) rec f t
    = apply fc (IVar fc (UN $ Basic "bimap"))
      (functorFun (assert <|> Just True) sp1 rec f Nothing
      :: functorFun (assert <|> Just True) sp2 rec f Nothing
      :: toList t)
  functorFun assert (FIBifun _ _ sp (Right _)) rec f t
    = apply fc (IVar fc (UN $ Basic "mapFst"))
      (functorFun (assert <|> Just True) sp rec f Nothing
      :: toList t)
  functorFun assert (FIPi {rig, pinfo, nm} dn sp) rec f t
    = optionallyEta fc t $ \ arg =>
      let nm = fromMaybe (UN $ Basic "x") nm in
      -- /!\ We cannot use the type stored in FIPi here because it could just
      -- be a name that will happen to be different when bound on the LHS!
      -- Cf. the Free test case in reflection017
      ILam fc rig pinfo (Just nm) (Implicit fc False) $
      functorFun assert sp rec f
        $ Just $ IApp fc arg
        $ functorFun assert dn rec f (Just (IVar fc nm))
  functorFun assert (FIFree y) rec f t = fromMaybe `(id) t

------------------------------------------------------------------------------
-- User-facing: Functor deriving

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
        let Just (MkConstructorView (paraz :< (para, _)) args) = constructorView ty
              | _ => throwError ConfusingReturnType
        let paras = paraz <>> []
        logMsg "derive.functor.clauses" 10 $
          "\{showPrefix True (dropNS cName)} (\{joinBy ", " (map (showPrec Dollar . mapTTImp cleanup . unArg . snd) args)})"
        let vars = map (map (IVar fc . un . ("x" ++) . show . (`minus` 1)))
                 $ zipWith (<$) [1..length args] (map snd args)

        -- only keep the arguments that are either:
        --  1. modified by map
        --  2. explicit
        recs <- for (zip vars args) $ \ (v, (rig, arg)) => do
                  res <- withError (WhenCheckingArg (mapTTImp cleanup $ unArg arg)) $
                           typeView {pol = Positive} f paras para (unArg arg)
                  pure $ case res of
                    Left sp => -- do not bother with assert_total if you're generating
                               -- a covering/partial definition
                               let useTot = False <$ guard (treq /= Total) in
                               pure (v, functorFun fc mutualWith useTot sp mapName funName . Just <$> v)
                    Right free => do ignore $ isExplicit v
                                     pure (v, v)
        let (vars, recs) = unzip (catMaybes recs)
        pure $ PatClause fc
          (apply fc (IVar fc mapName) [ fun, apply (IVar fc cName) vars])
          (apply (IVar fc cName) recs)

    -- Generate the type of the mapping function
    let paramNames = unArg . fst <$> params
    let a = un $ freshName paramNames "a"
    let b = un $ freshName paramNames "b"
    let va = IVar fc a
    let vb = IVar fc b
    logMsg "derive.functor.parameters" 20 $ unlines
      [ "Functors: \{show ns.asFunctors}"
      , "Bifunctors: \{show ns.asBifunctors}"
      , "Parameters: \{show (map (mapFst unArg) params)}"
      ]
    let ty = MkTy fc fc mapName $ withParams fc (paramConstraints ns) params
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

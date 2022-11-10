||| Deriving foldable instances using reflection
||| You can for instance define:
||| ```
||| data Tree a = Leaf a | Node (Tree a) (Tree a)
||| treeFoldable : Foldable Tree
||| treeFoldable = %runElab derive
||| ```

module Deriving.Foldable

import public Control.Monad.Either
import public Control.Monad.State
import public Data.List1
import public Data.Maybe
import public Data.Morphisms
import public Decidable.Equality
import public Language.Reflection

import public Deriving.Common

%language ElabReflection
%default total

public export
fromFoldMap :
  (0 f : Type -> Type) ->
  (forall a, b. Monoid b => (a -> b) -> f a -> b) ->
  Foldable f
fromFoldMap f fm = MkFoldable
  foldr
  foldl
  (foldr (\_, _ => False) True)
  (\ cons => foldl (\ acc, x => acc >>= flip cons x) . pure)
  (foldr (::) [])
  fm

  where

    foldr : forall a, b. (a -> b -> b) -> b -> f a -> b
    foldr cons base t = applyEndo (fm (Endo . cons) t) base

    foldl : forall a, b. (b -> a -> b) -> b -> f a -> b
    foldl cons base t = foldr (flip (.) . flip cons) id t base

------------------------------------------------------------------------------
-- Errors

||| Possible errors for the functor-deriving machinery.
public export
data Error : Type where
  NotFreeOf : Name -> TTImp -> Error
  NotAnApplication : TTImp -> Error
  NotAFoldable : TTImp -> Error
  NotABifoldable : TTImp -> Error
  NotFoldableInItsLastArg : TTImp -> Error
  UnsupportedType : TTImp -> Error
  NotAFiniteStructure : Error
  NotAnUnconstrainedValue : Count -> Error
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
    go acc (NotAnApplication s) = acc <>> ["The type \{show s} is not an application"]
    go acc (NotAFoldable s) = acc <>> ["Couldn't find a `Foldable' instance for the type constructor \{show s}"]
    go acc (NotABifoldable s) = acc <>> ["Couldn't find a `Bifoldable' instance for the type constructor \{show s}"]
    go acc (NotFoldableInItsLastArg s) = acc <>> ["Not foldable in its last argument \{show s}"]
    go acc (UnsupportedType s) = acc <>> ["Unsupported type \{show s}"]
    go acc NotAFiniteStructure = acc <>> ["Cannot fold over an infinite structure"]
    go acc (NotAnUnconstrainedValue rig) = acc <>> ["Cannot fold over a \{enunciate rig} value"]
    go acc InvalidGoal = acc <>> ["Expected a goal of the form `Foldable f`"]
    go acc ConfusingReturnType = acc <>> ["Confusing telescope"]
    go acc (WhenCheckingConstructor nm err) = go (acc :< "When checking constructor \{show nm}") err
    go acc (WhenCheckingArg s err) = go (acc :< "When checking argument of type \{show s}") err

record Parameters where
  constructor MkParameters
  asFoldables : List Nat
  asBifoldables : List Nat

initParameters : Parameters
initParameters = MkParameters [] []

paramConstraints : Parameters -> Nat -> Maybe TTImp
paramConstraints params pos
    = IVar emptyFC `{Prelude.Interfaces.Foldable}   <$ guard (pos `elem` params.asFoldables)
  <|> IVar emptyFC `{Prelude.Interfaces.Bifoldable} <$ guard (pos `elem` params.asBifoldables)

------------------------------------------------------------------------------
-- Core machinery: being foldable

-- Not meant to be re-exported as it's using the internal notion of error
isFreeOf' :
  {0 m : Type -> Type} ->
  {auto elab : Elaboration m} ->
  {auto error : MonadError Error m} ->
  (x : Name) -> (ty : TTImp) -> m (IsFreeOf x ty)
isFreeOf' x ty = case isFreeOf x ty of
  Nothing => throwError (NotFreeOf x ty)
  Just prf => pure prf

||| IsFoldableIn is parametrised by
||| @ t  the name of the data type whose constructors are being analysed
||| @ x  the name of the type variable that the foldable action will act on
||| @ ty the type being analysed
||| The inductive type delivers a proof that x can be folded over in ty,
||| assuming that t also is foldable.
public export
data IsFoldableIn : (t, x : Name) -> (ty : TTImp) -> Type where
  ||| The type variable x occurs alone
  FIVar : IsFoldableIn t x (IVar fc x)
  ||| There is a recursive subtree of type (t a1 ... an u) and u is Foldable in x.
  ||| We do not insist that u is exactly x so that we can deal with nested types
  ||| like the following:
  |||   data Full a = Leaf a | Node (Full (a, a))
  |||   data Term a = Var a | App (Term a) (Term a) | Lam (Term (Maybe a))
  FIRec : (0 _ : IsAppView (_, t) _ f) -> IsFoldableIn t x arg ->
          IsFoldableIn t x (IApp fc f arg)
  ||| The subterm is delayed (Lazy only, we can't fold over infinite structures)
  FIDelayed : IsFoldableIn t x ty -> IsFoldableIn t x (IDelayed fc LLazy ty)
  ||| There are nested subtrees somewhere inside a 3rd party type constructor
  ||| which satisfies the Bifoldable interface
  FIBifold : IsFreeOf x sp -> HasImplementation Bifoldable sp ->
             IsFoldableIn t x arg1 -> Either (IsFoldableIn t x arg2) (IsFreeOf x arg2) ->
             IsFoldableIn t x (IApp fc1 (IApp fc2 sp arg1) arg2)
  ||| There are nested subtrees somewhere inside a 3rd party type constructor
  ||| which satisfies the Foldable interface
  FIFold : IsFreeOf x sp -> HasImplementation Foldable sp ->
           IsFoldableIn t x arg -> IsFoldableIn t x (IApp fc sp arg)
  ||| A type free of x is trivially Foldable in it
  FIFree : IsFreeOf x a -> IsFoldableIn t x a

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
  |||   1. either that it is foldable in x
  |||   2. or that it is free of x
  ||| If it is not the case, we will use the `MonadError Error` constraint
  ||| to fail with an informative message.
  public export
  TypeView : TTImp -> Type
  TypeView ty = Either (IsFoldableIn t x ty) (IsFreeOf x ty)

  export
  fromTypeView : TypeView ty -> IsFoldableIn t x ty
  fromTypeView (Left prf) = prf
  fromTypeView (Right fo) = FIFree fo

  ||| Hoping to observe that ty is foldable
  export
  typeView : (ty : TTImp) -> m (TypeView ty)

  ||| To avoid code duplication in typeView, we have an auxiliary function
  ||| specifically to handle the application case
  typeAppView :
    {fc : FC} ->
    {f : TTImp} -> IsFreeOf x f ->
    (arg : TTImp) ->
    m (TypeView (IApp fc f arg))

  typeAppView {fc, f} isFO arg = do
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
          Yes Refl => pure $ Left (FIRec prf sp)
          No diff => case !(hasImplementation Foldable f) of
            Just prf => pure (Left (FIFold isFO prf sp))
            Nothing => case lookup hd ps of
              Just n => do
                -- record that the nth parameter should be functorial
                ns <- gets asFoldables
                let ns = ifThenElse (n `elem` ns) ns (n :: ns)
                modify { asFoldables := ns }
                -- and happily succeed
                logMsg "derive.foldable.assumption" 10 $
                  "I am assuming that the parameter \{show hd} is a Foldable"
                pure (Left (FIFold isFO assert_hasImplementation sp))
              Nothing => throwError (NotAFoldable f)
      -- Otherwise it better be the case that f is also free of x so that
      -- we can mark the whole type as being x-free.
      Right fo => do
        Right _ <- typeView f
          | _ => throwError $ NotFoldableInItsLastArg (IApp fc f arg)
        pure (Right assert_IsFreeOf)

  typeView tm@(IVar fc y) = case decEq x y of
    Yes Refl => pure (Left FIVar)
    No _ => pure (Right assert_IsFreeOf)
  typeView fab@(IApp _ (IApp fc1 f arg1) arg2) = do
    chka1 <- typeView arg1
    case chka1 of
      Right _ => do isFO <- isFreeOf' x (IApp _ f arg1)
                    typeAppView {f = assert_smaller fab (IApp _ f arg1)} isFO arg2
      Left sp => do
        isFO <- isFreeOf' x f
        case !(hasImplementation Bifoldable f) of
          Just prf => pure (Left (FIBifold isFO prf sp !(typeView arg2)))
          Nothing => do
            let Just (MkAppView (_, hd) ts prf) = appView f
               | _ => throwError (NotAnApplication f)
            case lookup hd ps of
              Just n => do
                -- record that the nth parameter should be bifoldable
                ns <- gets asBifoldables
                let ns = ifThenElse (n `elem` ns) ns (n :: ns)
                modify { asBifoldables := ns }
                -- and happily succeed
                logMsg "derive.foldable.assumption" 10 $
                    "I am assuming that the parameter \{show hd} is a Bifoldable"
                pure (Left (FIBifold isFO assert_hasImplementation sp !(typeView arg2)))
              Nothing => throwError (NotABifoldable f)
  typeView (IApp _ f arg) = do
    isFO <- isFreeOf' x f
    typeAppView isFO arg
  typeView (IDelayed _ lz f) = case !(typeView f) of
    Left sp => case lz of
      LLazy => pure (Left (FIDelayed sp))
      _ => throwError NotAFiniteStructure
    Right _ => pure (Right assert_IsFreeOf)
  typeView (IPrimVal _ _) = pure (Right assert_IsFreeOf)
  typeView (IType _) = pure (Right assert_IsFreeOf)
  typeView ty = case isFreeOf x ty of
    Nothing => throwError (UnsupportedType ty)
    Just prf => pure (Right prf)

------------------------------------------------------------------------------
-- Core machinery: building the foldMap function from an IsFoldableIn proof

parameters (fc : FC) (mutualWith : List Name)

  ||| foldMapFun takes
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
  foldMapFun : (assert : Maybe Bool) -> {ty : TTImp} -> IsFoldableIn t x ty ->
               (rec, f : Name) -> (arg : Maybe TTImp) -> TTImp
  foldMapFun assert FIVar rec f t = apply fc (IVar fc f) (toList t)
  foldMapFun assert (FIRec y sp) rec f t
    -- only add assert_total if it is declared to be needed
    = ifThenElse (fromMaybe False assert) (IApp fc (IVar fc (UN $ Basic "assert_total"))) id
    $ apply fc (IVar fc rec) (foldMapFun (Just False) sp rec f Nothing :: toList t)
  foldMapFun assert (FIDelayed sp) rec f Nothing
    -- here we need to eta-expand to avoid "Lazy t does not unify with t" errors
    = let nm = UN $ Basic "eta" in
      ILam fc MW ExplicitArg (Just nm) (IDelayed fc LLazy (Implicit fc False))
    $ foldMapFun assert sp rec f (Just (IVar fc nm))
  foldMapFun assert (FIDelayed sp) rec f (Just t)
    = foldMapFun assert sp rec f (Just t)
  foldMapFun assert {ty = IApp _ ty _} (FIFold _ _ sp) rec f t
    -- only add assert_total if we are calling a mutually defined Foldable implementation.
    = let isMutual = fromMaybe False (appView ty >>= \ v => pure (snd v.head `elem` mutualWith)) in
      ifThenElse isMutual (IApp fc (IVar fc (UN $ Basic "assert_total"))) id
    $ apply fc (IVar fc (UN $ Basic "foldMap"))
      (foldMapFun ((False <$ guard isMutual) <|> assert <|> Just True) sp rec f Nothing
       :: toList t)
  foldMapFun assert (FIBifold _ _ sp1 (Left sp2)) rec f t
    = apply fc (IVar fc (UN $ Basic "bifoldMap"))
      (foldMapFun (assert <|> Just True) sp1 rec f Nothing
      :: foldMapFun (assert <|> Just True) sp2 rec f Nothing
      :: toList t)
  foldMapFun assert (FIBifold _ _ sp (Right _)) rec f t
    = apply fc (IVar fc (UN $ Basic "bifoldMapFst"))
      (foldMapFun (assert <|> Just True) sp rec f Nothing
      :: toList t)
  foldMapFun assert (FIFree y) rec f t = `(mempty)

------------------------------------------------------------------------------
-- User-facing: Foldable deriving

namespace Foldable

  derive' : (Elaboration m, MonadError Error m) =>
            {default Private vis : Visibility} ->
            {default Total treq : TotalReq} ->
            {default [] mutualWith : List Name} ->
            m (Foldable f)
  derive' = do

    -- expand the mutualwith names to have the internal, fully qualified, names
    mutualWith <- map concat $ for mutualWith $ \ nm => do
                    ntys <- getType nm
                    pure (fst <$> ntys)

    -- The goal should have the shape (Foldable t)
    Just (IApp _ (IVar _ foldable) t) <- goal
      | _ => throwError InvalidGoal
    when (`{Prelude.Interfaces.Foldable} /= foldable) $
      logMsg "derive.foldable" 1 "Expected to derive Foldable but got \{show foldable}"

    -- t should be a type constructor
    logMsg "derive.foldable" 1 "Deriving Foldable for \{showPrec App $ mapTTImp cleanup t}"
    MkIsType f params cs <- isType t
    logMsg "derive.foldable.constructors" 1 $
      joinBy "\n" $ "" :: map (\ (n, ty) => "  \{showPrefix True $ dropNS n} : \{show $ mapTTImp cleanup ty}") cs

    -- Generate a clause for each data constructor
    let fc = emptyFC
    let un = UN . Basic
    let foldMapName = un ("foldMap" ++ show (dropNS f))
    let funName = un "f"
    let fun  = IVar fc funName
    (ns, cls) <- runStateT {m = m} initParameters $ for cs $ \ (cName, ty) =>
      withError (WhenCheckingConstructor cName) $ do
        -- Grab the types of the constructor's explicit arguments
        let Just (MkConstructorView (paraz :< (para, _)) args) = constructorView ty
              | _ => throwError ConfusingReturnType
        let paras = paraz <>> []
        logMsg "derive.foldable.clauses" 10 $
          "\{showPrefix True (dropNS cName)} (\{joinBy ", " (map (showPrec Dollar . mapTTImp cleanup . unArg . snd) args)})"
        let vars = map (map (IVar fc . un . ("x" ++) . show . (`minus` 1)))
                 $ zipWith (<$) [1..length args] (map snd args)
        recs <- for (zip vars args) $ \ (v, (rig, arg)) => do
                  res <- withError (WhenCheckingArg (mapTTImp cleanup (unArg arg))) $ do
                           res <- typeView f paras para (unArg arg)
                           case res of
                             Left _ => case rig of
                               MW => pure ()
                               _ => throwError (NotAnUnconstrainedValue rig)
                             _ => pure ()
                           pure res
                  pure $ case res of
                    Left sp => -- do not bother with assert_total if you're generating
                               -- a covering/partial definition
                               let useTot = False <$ guard (treq /= Total) in
                               Just (v, Just (foldMapFun fc mutualWith useTot sp foldMapName funName (Just $ unArg v)))
                    Right free => do ignore $ isExplicit v
                                     Just (v, Nothing)
        let (vars, recs) = unzip (catMaybes recs)
        pure $ PatClause fc
          (apply fc (IVar fc foldMapName) [ fun, apply (IVar fc cName) vars])
          (case catMaybes recs of
             [] => `(neutral)
             (x :: xs) => foldr1 (\v, vs => `(~(v) <+> ~(vs))) (x ::: xs))

    -- Generate the type of the mapping function
    let paramNames = unArg . fst <$> params
    let a = un $ freshName paramNames "a"
    let b = un $ freshName paramNames "b"
    let va = IVar fc a
    let vb = IVar fc b
    let ty = MkTy fc fc foldMapName $ withParams fc (paramConstraints ns) params
           $ IPi fc M0 ImplicitArg (Just a) (IType fc)
           $ IPi fc M0 ImplicitArg (Just b) (IType fc)
           $ `(Monoid ~(vb) => (~(va) -> ~(vb)) -> ~(t) ~(va) -> ~(vb))
    logMsg "derive.foldable.clauses" 1 $
      joinBy "\n" ("" :: ("  " ++ show (mapITy cleanup ty))
                      :: map (("  " ++) . showClause InDecl . mapClause cleanup) cls)

    -- Define the instance
    check $ ILocal fc
      [ IClaim fc MW vis [Totality treq] ty
      , IDef fc foldMapName cls
      ] `(fromFoldMap ~(t) ~(IVar fc foldMapName))

  ||| Derive an implementation of Foldable for a type constructor.
  ||| This can be used like so:
  ||| ```
  ||| data Tree a = Leaf a | Node (Tree a) (Tree a)
  ||| treeFoldable : Foldable Tree
  ||| treeFoldable = %runElab derive
  ||| ```
  export
  derive : {default Private vis : Visibility} ->
           {default Total treq : TotalReq} ->
           {default [] mutualWith : List Name} ->
           Elab (Foldable f)
  derive = do
    res <- runEitherT {e = Error, m = Elab} (derive' {vis, treq, mutualWith})
    case res of
      Left err => fail (show err)
      Right prf => pure prf

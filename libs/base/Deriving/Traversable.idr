||| Deriving traversable instances using reflection
||| You can for instance define:
||| ```
||| data Tree a = Leaf a | Node (Tree a) (Tree a)
||| treeFoldable : Traversable Tree
||| treeFoldable = %runElab derive
||| ```

module Deriving.Traversable

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

------------------------------------------------------------------------------
-- Errors

||| Possible errors for the functor-deriving machinery.
public export
data Error : Type where
  NotFreeOf : Name -> TTImp -> Error
  NotAnApplication : TTImp -> Error
  NotATraversable : TTImp -> Error
  NotABitraversable : TTImp -> Error
  NotTraversableInItsLastArg : TTImp -> Error
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
    go acc (NotATraversable s) = acc <>> ["Couldn't find a `Traversable' instance for the type constructor \{show s}"]
    go acc (NotABitraversable s) = acc <>> ["Couldn't find a `Bitraversable' instance for the type constructor \{show s}"]
    go acc (NotTraversableInItsLastArg s) = acc <>> ["Not traversable in its last argument \{show s}"]
    go acc (UnsupportedType s) = acc <>> ["Unsupported type \{show s}"]
    go acc NotAFiniteStructure = acc <>> ["Cannot traverse an infinite structure"]
    go acc (NotAnUnconstrainedValue rig) = acc <>> ["Cannot traverse a \{enunciate rig} value"]
    go acc InvalidGoal = acc <>> ["Expected a goal of the form `Traversable f`"]
    go acc ConfusingReturnType = acc <>> ["Confusing telescope"]
    go acc (WhenCheckingConstructor nm err) = go (acc :< "When checking constructor \{show nm}") err
    go acc (WhenCheckingArg s err) = go (acc :< "When checking argument of type \{show s}") err

record Parameters where
  constructor MkParameters
  asTraversables : List Nat
  asBitraversables : List Nat

initParameters : Parameters
initParameters = MkParameters [] []

paramConstraints : Parameters -> Nat -> Maybe TTImp
paramConstraints params pos
    = IVar emptyFC `{Prelude.Interfaces.Traversable}   <$ guard (pos `elem` params.asTraversables)
  <|> IVar emptyFC `{Prelude.Interfaces.Bitraversable} <$ guard (pos `elem` params.asBitraversables)

------------------------------------------------------------------------------
-- Core machinery: being traversable

-- Not meant to be re-exported as it's using the internal notion of error
isFreeOf' :
  {0 m : Type -> Type} ->
  {auto elab : Elaboration m} ->
  {auto error : MonadError Error m} ->
  (x : Name) -> (ty : TTImp) -> m (IsFreeOf x ty)
isFreeOf' x ty = case isFreeOf x ty of
  Nothing => throwError (NotFreeOf x ty)
  Just prf => pure prf

||| IsTraversableIn is parametrised by
||| @ t  the name of the data type whose constructors are being analysed
||| @ x  the name of the type variable that the traversable action will act on
||| @ ty the type being analysed
||| The inductive type delivers a proof that x can be traversed over in ty,
||| assuming that t also is traversable.
public export
data IsTraversableIn : (t, x : Name) -> (ty : TTImp) -> Type where
  ||| The type variable x occurs alone
  TIVar : IsTraversableIn t x (IVar fc x)
  ||| There is a recursive subtree of type (t a1 ... an u) and u is Traversable in x.
  ||| We do not insist that u is exactly x so that we can deal with nested types
  ||| like the following:
  |||   data Full a = Leaf a | Node (Full (a, a))
  |||   data Term a = Var a | App (Term a) (Term a) | Lam (Term (Maybe a))
  TIRec : (0 _ : IsAppView (_, t) _ f) -> IsTraversableIn t x arg ->
          IsTraversableIn t x (IApp fc f arg)
  ||| The subterm is delayed (Lazy only, we can't traverse infinite structures)
  TIDelayed : IsTraversableIn t x ty -> IsTraversableIn t x (IDelayed fc LLazy ty)
  ||| There are nested subtrees somewhere inside a 3rd party type constructor
  ||| which satisfies the Bitraversable interface
  TIBifold : IsFreeOf x sp -> HasImplementation Bitraversable sp ->
             IsTraversableIn t x arg1 -> Either (IsTraversableIn t x arg2) (IsFreeOf x arg2) ->
             IsTraversableIn t x (IApp fc1 (IApp fc2 sp arg1) arg2)
  ||| There are nested subtrees somewhere inside a 3rd party type constructor
  ||| which satisfies the Traversable interface
  TIFold : IsFreeOf x sp -> HasImplementation Traversable sp ->
           IsTraversableIn t x arg -> IsTraversableIn t x (IApp fc sp arg)
  ||| A type free of x is trivially Traversable in it
  TIFree : IsFreeOf x a -> IsTraversableIn t x a

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
  |||   1. either that it is traversable in x
  |||   2. or that it is free of x
  ||| If it is not the case, we will use the `MonadError Error` constraint
  ||| to fail with an informative message.
  public export
  TypeView : TTImp -> Type
  TypeView ty = Either (IsTraversableIn t x ty) (IsFreeOf x ty)

  export
  fromTypeView : TypeView ty -> IsTraversableIn t x ty
  fromTypeView (Left prf) = prf
  fromTypeView (Right fo) = TIFree fo

  ||| Hoping to observe that ty is traversable
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
          Yes Refl => pure $ Left (TIRec prf sp)
          No diff => case !(hasImplementation Traversable f) of
            Just prf => pure (Left (TIFold isFO prf sp))
            Nothing => case lookup hd ps of
              Just n => do
                -- record that the nth parameter should be functorial
                ns <- gets asTraversables
                let ns = ifThenElse (n `elem` ns) ns (n :: ns)
                modify { asTraversables := ns }
                -- and happily succeed
                logMsg "derive.traversable.assumption" 10 $
                  "I am assuming that the parameter \{show hd} is a Traversable"
                pure (Left (TIFold isFO assert_hasImplementation sp))
              Nothing => throwError (NotATraversable f)
      -- Otherwise it better be the case that f is also free of x so that
      -- we can mark the whole type as being x-free.
      Right fo => do
        Right _ <- typeView f
          | _ => throwError $ NotTraversableInItsLastArg (IApp fc f arg)
        pure (Right assert_IsFreeOf)

  typeView tm@(IVar fc y) = case decEq x y of
    Yes Refl => pure (Left TIVar)
    No _ => pure (Right assert_IsFreeOf)
  typeView fab@(IApp _ (IApp fc1 f arg1) arg2) = do
    chka1 <- typeView arg1
    case chka1 of
      Right _ => do isFO <- isFreeOf' x (IApp _ f arg1)
                    typeAppView {f = assert_smaller fab (IApp _ f arg1)} isFO arg2
      Left sp => do
        isFO <- isFreeOf' x f
        case !(hasImplementation Bitraversable f) of
          Just prf => pure (Left (TIBifold isFO prf sp !(typeView arg2)))
          Nothing => do
            let Just (MkAppView (_, hd) ts prf) = appView f
               | _ => throwError (NotAnApplication f)
            case lookup hd ps of
              Just n => do
                -- record that the nth parameter should be bitraversable
                ns <- gets asBitraversables
                let ns = ifThenElse (n `elem` ns) ns (n :: ns)
                modify { asBitraversables := ns }
                -- and happily succeed
                logMsg "derive.traversable.assumption" 10 $
                    "I am assuming that the parameter \{show hd} is a Bitraversable"
                pure (Left (TIBifold isFO assert_hasImplementation sp !(typeView arg2)))
              Nothing => throwError (NotABitraversable f)
  typeView (IApp _ f arg) = do
    isFO <- isFreeOf' x f
    typeAppView isFO arg
  typeView (IDelayed _ lz f) = case !(typeView f) of
    Left sp => case lz of
      LLazy => pure (Left (TIDelayed sp))
      _ => throwError NotAFiniteStructure
    Right _ => pure (Right assert_IsFreeOf)
  typeView (IPrimVal _ _) = pure (Right assert_IsFreeOf)
  typeView (IType _) = pure (Right assert_IsFreeOf)
  typeView ty = case isFreeOf x ty of
    Nothing => throwError (UnsupportedType ty)
    Just prf => pure (Right prf)

------------------------------------------------------------------------------
-- Core machinery: building the traverse function from an IsTraversableIn proof

parameters (fc : FC) (mutualWith : List Name)

  ||| traverseFun takes
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
  traverseFun : (assert : Maybe Bool) -> {ty : TTImp} -> IsTraversableIn t x ty ->
                (rec, f : Name) -> (arg : Maybe TTImp) -> TTImp
  traverseFun assert TIVar rec f t = apply fc (IVar fc f) (toList t)
  traverseFun assert (TIRec y sp) rec f t
    -- only add assert_total if it is declared to be needed
    = ifThenElse (fromMaybe False assert) (IApp fc (IVar fc (UN $ Basic "assert_total"))) id
    $ apply fc (IVar fc rec) (traverseFun (Just False) sp rec f Nothing :: toList t)
  traverseFun assert (TIDelayed sp) rec f Nothing
    -- here we need to eta-expand to avoid "Lazy t does not unify with t" errors
    = let nm = UN $ Basic "eta" in
      ILam fc MW ExplicitArg (Just nm) (IDelayed fc LLazy (Implicit fc False))
    $ apply fc `((<$>))
    [ `(delay)
    , traverseFun assert sp rec f (Just (IVar fc nm))
    ]
  traverseFun assert (TIDelayed sp) rec f (Just t)
    = apply fc `((<$>))
    [ `(delay)
    , traverseFun assert sp rec f (Just t)
    ]
  traverseFun assert {ty = IApp _ ty _} (TIFold _ _ sp) rec f t
    -- only add assert_total if we are calling a mutually defined Traversable implementation.
    = let isMutual = fromMaybe False (appView ty >>= \ v => pure (snd v.head `elem` mutualWith)) in
      ifThenElse isMutual (IApp fc (IVar fc (UN $ Basic "assert_total"))) id
    $ apply fc (IVar fc (UN $ Basic "traverse"))
      (traverseFun ((False <$ guard isMutual) <|> assert <|> Just True) sp rec f Nothing
       :: toList t)
  traverseFun assert (TIBifold _ _ sp1 (Left sp2)) rec f t
    = apply fc (IVar fc (UN $ Basic "bitraverse"))
      (traverseFun (assert <|> Just True) sp1 rec f Nothing
      :: traverseFun (assert <|> Just True) sp2 rec f Nothing
      :: toList t)
  traverseFun assert (TIBifold _ _ sp (Right _)) rec f t
    = apply fc (IVar fc (UN $ Basic "bitraverseFst"))
      (traverseFun (assert <|> Just True) sp rec f Nothing
      :: toList t)
  traverseFun assert (TIFree y) rec f t = `(mempty)

------------------------------------------------------------------------------
-- User-facing: Traversable deriving

applyA : FC -> TTImp -> List (Either (Argument TTImp) TTImp) -> TTImp
applyA fc c [] = `(pure ~(c))
applyA fc c (Right a :: as) = applyA fc (IApp fc c a) as
applyA fc c as =
  let (pref, suff) = spanBy canBeApplied ([<] <>< as) in
  let (lams, args, vals) = preEta 0 (pref <>> []) in
  let eta = foldr (\ x => ILam fc MW ExplicitArg (Just x) (Implicit fc False)) (apply c args) lams in
  fire eta (map Left vals ++ (suff <>> []))

  where

    canBeApplied : Either (Argument TTImp) TTImp -> Maybe (Either TTImp TTImp)
    canBeApplied (Left (Arg _ t)) = pure (Left t)
    canBeApplied (Right t) = pure (Right t)
    canBeApplied _ = Nothing

    preEta : Nat -> List (Either (Argument TTImp) TTImp) ->
             (List Name, List (Argument TTImp), List TTImp)
    preEta n [] = ([], [], [])
    preEta n (a :: as) =
      let (n, ns, args, vals) = the (Nat, List Name, List (Argument TTImp), List _) $
            let x = UN (Basic ("y" ++ show n)); vx = IVar fc x in case a of
              Left (Arg fc t) => (S n, [x], [Arg fc vx], [t])
              Left (NamedArg fc nm t) => (S n, [x], [NamedArg fc nm vx], [t])
              Left (AutoArg fc t) => (S n, [x], [AutoArg fc vx], [t])
              Right t => (n, [], [Arg fc t], [])
      in
      let (nss, argss, valss) = preEta n as in
      (ns ++ nss, args ++ argss, vals ++ valss)

    go : TTImp -> List (Either TTImp TTImp) -> TTImp
    go f [] = f
    go f (Left a :: as) = go (apply fc `((<*>)) [f, a]) as
    go f (Right a :: as) = go (apply fc `((<*>)) [f, IApp fc `(pure) a]) as

    fire : TTImp -> List (Either TTImp TTImp) -> TTImp
    fire f [] = f
    fire f (a :: as) = go (apply fc `((<$>)) [f, either id id a]) as

namespace Traversable

  derive' : (Elaboration m, MonadError Error m) =>
            {default Private vis : Visibility} ->
            {default Total treq : TotalReq} ->
            {default [] mutualWith : List Name} ->
            m (Traversable f)
  derive' = do

    -- expand the mutualwith names to have the internal, fully qualified, names
    mutualWith <- map concat $ for mutualWith $ \ nm => do
                    ntys <- getType nm
                    pure (fst <$> ntys)

    -- The goal should have the shape (Traversable t)
    Just (IApp _ (IVar _ traversable) t) <- goal
      | _ => throwError InvalidGoal
    when (`{Prelude.Interfaces.Traversable} /= traversable) $
      logMsg "derive.traversable" 1 "Expected to derive Traversable but got \{show traversable}"

    -- t should be a type constructor
    logMsg "derive.traversable" 1 "Deriving Traversable for \{showPrec App $ mapTTImp cleanup t}"
    MkIsType f params cs <- isType t
    logMsg "derive.traversable.constructors" 1 $
      joinBy "\n" $ "" :: map (\ (n, ty) => "  \{showPrefix True $ dropNS n} : \{show $ mapTTImp cleanup ty}") cs

    -- Generate a clause for each data constructor
    let fc = emptyFC
    let un = UN . Basic
    let traverseName = un ("traverse" ++ show (dropNS f))
    let funName = un "f"
    let fun  = IVar fc funName
    (ns, cls) <- runStateT {m = m} initParameters $ for cs $ \ (cName, ty) =>
      withError (WhenCheckingConstructor cName) $ do
        -- Grab the types of the constructor's explicit arguments
        let Just (MkConstructorView (paraz :< (para, _)) args) = constructorView ty
              | _ => throwError ConfusingReturnType
        let paras = paraz <>> []
        logMsg "derive.traversable.clauses" 10 $
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
                               Just (v, Left (traverseFun fc mutualWith useTot sp traverseName funName . Just <$> v))
                    Right free => do ignore $ isExplicit v
                                     Just (v, Right (unArg v))
        let (vars, recs) = unzip (catMaybes recs)
        pure $ PatClause fc
          (apply fc (IVar fc traverseName) [ fun, apply (IVar fc cName) vars])
          (applyA fc (IVar fc cName) recs)

    -- Generate the type of the mapping function
    let paramNames = unArg . fst <$> params
    let a = un $ freshName paramNames "a"
    let b = un $ freshName paramNames "b"
    let f = un $ freshName paramNames "f"
    let va = IVar fc a
    let vb = IVar fc b
    let vf = IVar fc f
    let ty = MkTy fc fc traverseName $ withParams fc (paramConstraints ns) params
           $ IPi fc M0 ImplicitArg (Just a) (IType fc)
           $ IPi fc M0 ImplicitArg (Just b) (IType fc)
           $ IPi fc M0 ImplicitArg (Just f) (IPi fc MW ExplicitArg Nothing (IType fc) (IType fc))
           $ `(Applicative ~(vf) => (~(va) -> ~(vf) ~(vb)) -> ~(t) ~(va) -> ~(vf) (~(t) ~(vb)))
    logMsg "derive.traversable.clauses" 1 $
      joinBy "\n" ("" :: ("  " ++ show (mapITy cleanup ty))
                      :: map (("  " ++) . showClause InDecl . mapClause cleanup) cls)

    -- Define the instance
    check $ ILocal fc
      [ IClaim fc MW vis [Totality treq] ty
      , IDef fc traverseName cls
      ] `(MkTraversable {t = ~(t)} ~(IVar fc traverseName))

  ||| Derive an implementation of Traversable for a type constructor.
  ||| This can be used like so:
  ||| ```
  ||| data Tree a = Leaf a | Node (Tree a) (Tree a)
  ||| treeTraversable : Traversable Tree
  ||| treeTraversable = %runElab derive
  ||| ```
  export
  derive : {default Private vis : Visibility} ->
           {default Total treq : TotalReq} ->
           {default [] mutualWith : List Name} ->
           Elab (Traversable f)
  derive = do
    res <- runEitherT {e = Error, m = Elab} (derive' {vis, treq, mutualWith})
    case res of
      Left err => fail (show err)
      Right prf => pure prf

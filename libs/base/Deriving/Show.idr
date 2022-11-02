||| Deriving show instances using reflection
||| You can for instance define:
||| ```
||| data Tree a = Leaf a | Node (Tree a) (Tree a)
||| treeShow : Show a => Show (Tree a)
||| treeShow = %runElab derive
||| ```

module Deriving.Show

import public Control.Monad.Either
import public Control.Monad.State
import public Data.Maybe
import public Decidable.Equality
import public Language.Reflection

import public Deriving.Common

%language ElabReflection
%default total

public export
fromShowPrec :
  (Prec -> ty -> String) ->
  Show ty
fromShowPrec sp = MkShow (sp Open) sp

------------------------------------------------------------------------------
-- Errors

||| Possible errors for the functor-deriving machinery.
public export
data Error : Type where
  NotAShowable : Name -> Error
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
    go acc (NotAShowable nm) = acc <>> ["Couldn't find a `Show' instance for the type \{show nm}"]
    go acc (UnsupportedType s) = acc <>> ["Unsupported type \{show s}"]
    go acc NotAFiniteStructure = acc <>> ["Cannot show an infinite structure"]
    go acc (NotAnUnconstrainedValue rig) = acc <>> ["Cannot show a \{enunciate rig} value"]
    go acc InvalidGoal = acc <>> ["Expected a goal of the form `Show t`"]
    go acc ConfusingReturnType = acc <>> ["Confusing telescope"]
    go acc (WhenCheckingConstructor nm err) = go (acc :< "When checking constructor \{show nm}") err
    go acc (WhenCheckingArg s err) = go (acc :< "When checking argument of type \{show s}") err

record Parameters where
  constructor MkParameters
  asShowables : List Nat

initParameters : Parameters
initParameters = MkParameters []

paramConstraints : Parameters -> Nat -> Maybe TTImp
paramConstraints params pos
    = IVar emptyFC `{Prelude.Show.Show} <$ guard (pos `elem` params.asShowables)

------------------------------------------------------------------------------
-- Core machinery: being showable

ShowN : TTImp -> Name -> TTImp
ShowN ty nm = go (IVar emptyFC nm) ty Z where

  go : TTImp -> TTImp -> Nat -> TTImp
  go acc (IPi _ _ pinfo mn (IType _) ty) n
    = let var = MN "__param" (cast n) in
      IPi emptyFC M0 ImplicitArg (Just var) (Implicit emptyFC False)
    $ IPi emptyFC MW AutoImplicit Nothing (IApp emptyFC `(Show) (IVar emptyFC var))
    $ go (TTImp.apply acc (toList (fromPiInfo emptyFC pinfo mn (IVar emptyFC var)))) ty (S n)
  go acc (IPi _ _ pinfo mn _ ty) n
    = let var = MN "__param" (cast n) in
      IPi emptyFC M0 ImplicitArg (Just var) (Implicit emptyFC False)
    $ go (TTImp.apply acc (toList (fromPiInfo emptyFC pinfo mn (IVar emptyFC var)))) ty (S n)
  go acc _ _ = IApp emptyFC `(Show) acc

||| IsShowable is parametrised by
||| @ t  the name of the data type whose constructors are being analysed
||| @ ty the type being analysed
||| The inductive type delivers a proof that ty can be shown,
||| assuming that t also is showable.
public export
data IsShowable : (t : Name) -> (ty : TTImp) -> Type
data IsShowableArgs : (t : Name) -> (tconty : TTImp) -> (ty : List (Argument TTImp)) -> Type

data IsShowable : (t : Name) -> (ty : TTImp) -> Type where
  ||| The subterm is delayed (Lazy only, we can't traverse infinite structures)
  ISDelayed : IsShowable t ty -> IsShowable t (IDelayed fc LLazy ty)
  ||| There is a recursive subtree of type (t a1 ... an)
  ISRec : (0 _ : IsAppView (_, t) _ ty) -> IsShowable t ty
  ||| There are nested subtrees somewhere inside a 3rd party type constructor
  ||| which satisfies the Show interface
  ISShowN : (0 _ : IsAppView (_, tcon) args ty) ->
            HasType tcon tconty ->
            IsProvable (ShowN tconty tcon) ->
            IsShowableArgs t tconty (args <>> []) -> IsShowable t ty
  ||| Or we could be referring to one of the parameters
  ISParam : IsShowable t ty
  ||| A primitive type is trivially Showable
  ISPrim : (ty : PrimType) -> IsShowable t (IPrimVal fc (PrT ty))

data IsShowableArgs : (t : Name) -> (tconty : TTImp) -> (ty : List (Argument TTImp)) -> Type where
  Done : IsShowableArgs t tconty []
  Step :  IsShowable t (unArg arg) -> IsShowableArgs t ty args ->
         IsShowableArgs t (IPi fc1 r ExplicitArg mn (IType fc2) ty) (arg :: args)
  Drop : (forall fc. Not (dom === IType fc)) -> IsShowableArgs t ty args ->
         IsShowableArgs t (IPi fc1 r ExplicitArg mn dom ty) (arg :: args)
  Skip : Not (pinfo === ExplicitArg) -> IsShowableArgs t ty args ->
         IsShowableArgs t (IPi fc1 r pinfo mn dom ty) args -- TODO: constrain more?

parameters (fc : FC) (mutualWith : List Name)

  isRecs : IsShowableArgs t ty ts -> Bool
  isRec : IsShowable t ts -> Bool

  isRecs Done = False
  isRecs (Step x xs) = isRec x || isRecs xs
  isRecs (Drop f xs) = isRecs xs
  isRecs (Skip f xs) = isRecs xs

  isRec (ISDelayed x) = isRec x
  isRec (ISRec _) = True
  isRec (ISShowN _ _ _ xs) = isRecs xs
  isRec ISParam = False
  isRec (ISPrim _) = False

  showPrecFun : {ty : _} -> IsShowable t ty -> TTImp -> TTImp
  showPrecFun (ISDelayed p) t = showPrecFun p (IForce (getFC t) t)
  showPrecFun (ISRec _) t = IApp emptyFC `(assert_total) (IApp emptyFC `(showArg) t)
  showPrecFun {ty} (ISShowN _ _ _ as) t
    = let isMutual = fromMaybe False (appView ty >>= \ v => pure (snd v.head `elem` mutualWith)) in
      ifThenElse (isMutual || isRecs as) (IApp emptyFC `(assert_total)) id
    $ IApp emptyFC `(showArg) t
  showPrecFun ISParam t = IApp emptyFC  `(showArg) t
  showPrecFun (ISPrim pty) t = IApp emptyFC  `(showArg) t

parameters
  {0 m : Type -> Type}
  {auto elab : Elaboration m}
  {auto error : MonadError Error m}
  {auto cs : MonadState Parameters m}
  (t : Name)
  (ps : List (Name, Nat))

  ||| Hoping to observe that ty can be shown
  export
  typeView : (ty : TTImp) -> m (IsShowable t ty)
  typeViews : (tconty : TTImp) -> (tys : List (Argument TTImp)) ->
              m (IsShowableArgs t tconty tys)

  typeView (IDelayed _ lz ty) = case lz of
    LLazy => ISDelayed <$> typeView ty
    _ => throwError NotAFiniteStructure
  typeView (IPrimVal _ (PrT ty)) = pure (ISPrim ty)
  typeView ty = do
    let Just (MkAppView (_, hd) ts prf) = appView ty
      | _ => throwError (UnsupportedType ty)
    let No _ = decEq hd t
      | Yes Refl => pure (ISRec prf)
    Just (hdty ** hT) <- hasType hd
      | _ => case lookup hd ps <* guard (null ts) of
               Just n => do
                 -- record that the nth parameter should be showable
                 ns <- gets asShowables
                 let ns = ifThenElse (n `elem` ns) ns (n :: ns)
                 modify { asShowables := ns }
                 -- and happily succeed
                 logMsg "derive.show.assumption" 10 $
                   "I am assuming that the parameter \{show hd} can be shown"
                 pure ISParam
               _ => throwError (UnsupportedType ty)
    Just iP <- isProvable (ShowN hdty hd)
      | _ => throwError (NotAShowable hd)
    ISShowN prf hT iP <$> typeViews hdty (ts <>> [])

  typeViews _ [] = pure Done
  typeViews (IPi _ _ ExplicitArg _ (IType fc) ty) (t :: ts)
    = Step <$> assert_total (typeView (unArg t)) <*> typeViews ty ts
  typeViews (IPi _ _ ExplicitArg _ dom ty) (t :: ts)
    = Drop (\ x => believe_me x) <$> typeViews ty ts
  typeViews (IPi _ _ _ _ _ ty) ts
    = Skip (\ x => believe_me x) <$> typeViews ty ts
  typeViews ty ts = throwError (UnsupportedType ty)

namespace Show

  derive' : (Elaboration m, MonadError Error m) =>
            {default Private vis : Visibility} ->
            {default Total treq : TotalReq} ->
            {default [] mutualWith : List Name} ->
            m (Show f)
  derive' = do

    -- expand the mutualwith names to have the internal, fully qualified, names
    mutualWith <- map concat $ for mutualWith $ \ nm => do
                    ntys <- getType nm
                    pure (fst <$> ntys)

    -- The goal should have the shape (Show t)
    Just (IApp _ (IVar _ showable) t) <- goal
      | _ => throwError InvalidGoal
    when (`{Prelude.Show.Show} /= showable) $
      logMsg "derive.show" 1 "Expected to derive Show but got \{show showable}"

    -- t should be a type constructor
    logMsg "derive.show" 1 "Deriving Show for \{showPrec App $ mapTTImp cleanup t}"
    MkIsType f params cs <- isType t
    logMsg "derive.show.constructors" 1 $
      joinBy "\n" $ "" :: map (\ (n, ty) => "  \{showPrefix True $ dropNS n} : \{show $ mapTTImp cleanup ty}") cs

    -- Generate a clause for each data constructor
    let fc = emptyFC
    let un = UN . Basic
    let showName = un ("showPrec" ++ show (dropNS f))
    let precName = un "d"
    let prec = IVar fc precName
    (ns, cls) <- runStateT {m = m} initParameters $ for cs $ \ (cName, ty) =>
      withError (WhenCheckingConstructor cName) $ do
        -- Grab the types of the constructor's explicit arguments
        let Just (MkConstructorView paraz args) = constructorView ty
              | _ => throwError ConfusingReturnType
        logMsg "derive.show.clauses" 10 $
          "\{showPrefix True (dropNS cName)} (\{joinBy ", " (map (showPrec Dollar . mapTTImp cleanup . unArg . snd) args)})"
        -- Only keep the visible arguments
        let args = mapMaybe (bitraverse pure (map snd . isExplicit)) args
        -- Special case for constructors with no argument
        let (_ :: _) = args
          | [] => pure $ PatClause fc
                    (apply fc (IVar fc showName) [ prec, IVar fc cName])
                    (IPrimVal fc (Str (showPrefix True (dropNS cName))))

        let vars = zipWith (const . IVar fc . un . ("x" ++) . show . (`minus` 1)) [1..length args] args
        recs <- for (zip vars args) $ \ (v, (rig, ty)) => do

                  let MW = rig
                    | _ => throwError (NotAnUnconstrainedValue rig)

                  res <- withError (WhenCheckingArg (mapTTImp cleanup ty)) $ do
                           typeView f (paraz <>> []) ty
                  pure $ Just (showPrecFun fc mutualWith res v)

        let args = catMaybes recs
        let asList = foldr (\ a, as => apply fc (IVar fc `{Prelude.(::)}) [a,as]) `(Prelude.Nil)
        pure $ PatClause fc
          (apply fc (IVar fc showName) [ prec, apply fc (IVar fc cName) vars])
          (apply fc (IVar fc (un "showCon"))
            [ prec
            , IPrimVal fc (Str (showPrefix True (dropNS cName)))
            , case args of
                [a] => a
                _ => IApp fc (IVar fc (un "concat")) (asList args)
            ])

    -- Generate the type of the show function
    let ty = MkTy fc fc showName $ withParams fc (paramConstraints ns) params
           $ `(Prec -> ~(t) -> String)
    logMsg "derive.show.clauses" 1 $
      joinBy "\n" ("" :: ("  " ++ show (mapITy cleanup ty))
                      :: map (("  " ++) . showClause InDecl . mapClause cleanup) cls)

    -- Define the instance
    check $ ILocal fc
      [ IClaim fc MW vis [Totality treq] ty
      , IDef fc showName cls
      ] `(fromShowPrec ~(IVar fc showName))

  ||| Derive an implementation of Show for a type constructor.
  ||| This can be used like so:
  ||| ```
  ||| data Tree a = Leaf a | Node (Tree a) (Tree a)
  ||| treeShow : Show a => Show (Tree a)
  ||| treeShow = %runElab derive
  ||| ```
  export
  derive : {default Private vis : Visibility} ->
           {default Total treq : TotalReq} ->
           {default [] mutualWith : List Name} ->
           Elab (Show f)
  derive = do
    res <- runEitherT {e = Error, m = Elab} (derive' {vis, treq, mutualWith})
    case res of
      Left err => fail (show err)
      Right prf => pure prf

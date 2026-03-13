module Deriving.Common

import Data.SnocList
import Language.Reflection

%default total

------------------------------------------------------------------------------
-- Being free of a variable

||| IsFreeOf is parametrised by
||| @ x  the name of the type variable that the functorial action will change
||| @ ty the type that does not contain any mention of x
export
data IsFreeOf : (x : Name) -> (ty : TTImp) -> Type where
  ||| For now we do not bother keeping precise track of the proof that a type
  ||| is free of x
  TrustMeFO : IsFreeOf a x

||| We may need to manufacture proofs and so we provide the `assert` escape hatch.
export %unsafe
assert_IsFreeOf : IsFreeOf x ty
assert_IsFreeOf = TrustMeFO

||| Testing function deciding whether the given term is free of a particular
||| variable.
export
isFreeOf : (x : Name) -> (ty : TTImp) -> Maybe (IsFreeOf x ty)
isFreeOf x ty
  = do isOk <- flip mapMTTImp ty $ \case
         t@(IVar _ v) => t <$ guard (v /= x)
         t => pure t
       pure TrustMeFO

------------------------------------------------------------------------------
-- Being a (data) type

public export
data TypeParameter
  = MkTPLocal Name
  | MkTPPrim Constant
  | MkTPApp (Name, SnocList (Argument TypeParameter))
  | MkTPIType

export
Show TypeParameter where
  show (MkTPLocal a) = "MkTPLocal \{show a}"
  show (MkTPPrim c) = "MkTPPrim \{show c}"
  show (MkTPApp a) = "MkTPApp \{assert_total $ show (map (map unArg) a)}"
  show MkTPIType = "MkTPIType"

public export
record IsFamily where
  constructor MkIsFamily
  typeConstructor  : Name
  parameterNames   : List (Argument TypeParameter, Nat)
  dataConstructors : List (Name, TTImp)

wording : NameType -> String
wording Bound = "a bound variable"
wording Func = "a function name"
wording (DataCon tag arity) = "a data constructor"
wording (TyCon tag arity) = "a type constructor"

isTypeCon : Elaboration m => FC -> Name -> m (List (Name, TTImp))
isTypeCon fc ty = do
    [(_, MkNameInfo (TyCon _ _))] <- getInfo ty
      | [] => failAt fc "\{show ty} out of scope"
      | [(_, MkNameInfo nt)] => failAt fc "\{show ty} is \{wording nt} rather than a type constructor"
      | _ => failAt fc "\{show ty} is ambiguous"
    cs <- getCons ty
    for cs $ \ n => do
      [(_, ty)] <- getType n
         | _ => failAt fc "\{show n} is ambiguous"
      pure (n, ty)

toTypeParameter : Elaboration m => TTImp -> m TypeParameter
toTypeParameter (IType _) = pure MkTPIType
toTypeParameter (IPrimVal _ c) = pure (MkTPPrim c)
-- Unqualified: that's a local variable
toTypeParameter (IVar _ nm@(UN (Basic _))) = pure (MkTPLocal nm)
toTypeParameter arg with (appView arg)
  toTypeParameter t | Nothing = failAt (getFC t) "Unexpected a type parameter, got: \{show t}"
  toTypeParameter _ | (Just $ MkAppView (fc, h) args _) = do
    typedArgs <- assert_total $ traverse @{Compose} toTypeParameter args
    pure $ MkTPApp (h, typedArgs)

export
isFamily : Elaboration m => TTImp -> m IsFamily
isFamily = go Z [] where
  go : Nat -> List (Argument TypeParameter, Nat) -> TTImp -> m IsFamily
  go idx acc (IVar fc n) = MkIsFamily n (map (map (minus idx . S)) acc) <$> isTypeCon fc n
  go idx acc (IApp fc t arg) = go (S idx) ((Arg fc !(toTypeParameter arg), idx) :: acc) t
  go idx acc (INamedApp fc t nm arg) = go (S idx) ((NamedArg fc nm !(toTypeParameter arg), idx) :: acc) t
  go idx acc (IAutoApp fc t arg) = go (S idx) ((AutoArg fc !(toTypeParameter arg), idx) :: acc) t
  go idx acc t = failAt (getFC t) "Expected a type constructor, got: \{show t}"

------------------------------------------------------------------------------
-- Being a (data) constructor with a parameter
-- TODO: generalise?

public export
record ConstructorView where
  constructor MkConstructorView
  params      : SnocList (Name, Nat)
  conArgTypes : List (Count, Argument TTImp)

export
constructorView : TTImp -> Maybe ConstructorView
constructorView (IPi fc rig pinfo x a b) = do
  let Just arg = fromPiInfo fc pinfo x a
    | Nothing => constructorView b -- this better be a boring argument...
  let True = rig /= M1
    | False => constructorView b -- this better be another boring argument...
  { conArgTypes $= ((rig, arg) ::) } <$> constructorView b
constructorView f = do
  MkAppView _ ts _ <- appView f
  let range = [<] <>< [0..minus (length ts) 1]
  let ps = flip mapMaybe (zip ts range) $ \ t => the (Maybe (Name, Nat)) $ case t of
             (Arg _ (IVar _ nm), n) => Just (nm, n)
             _ => Nothing
  pure (MkConstructorView ps [])

------------------------------------------------------------------------------
-- Satisfying an interface
--
-- In order to derive Functor for `data Tree a = Node (List (Tree a))`, we need
-- to make sure that `Functor List` already exists. This is done using the following
-- convenience functions.

export
withParams : FC -> (Nat -> Maybe TTImp) -> List (Argument TypeParameter, Nat) -> TTImp -> TTImp
withParams fc params nms t = go nms where

  addConstraint : Maybe TTImp -> Name -> TTImp -> TTImp
  addConstraint Nothing _ = id
  addConstraint (Just cst) nm =
     let ty = IApp fc cst (IVar fc nm) in
     IPi fc MW AutoImplicit Nothing ty

  go : List (Argument TypeParameter, Nat) -> TTImp
  go [] = t
  go ((arg, pos) :: nms) with (unArg arg)
    go ((arg, pos) :: nms) | MkTPLocal nm =
      IPi fc M0 ImplicitArg (Just nm) (Implicit fc True)
      $ addConstraint (params pos) nm
      $ go nms
    go ((arg, pos) :: nms) | MkTPPrim _ = go nms
    go ((arg, pos) :: nms) | MkTPApp _ = go nms
    go ((arg, pos) :: nms) | MkTPIType  = go nms

||| Type of proofs that something has a given type
export
data HasType : (nm : Name) -> (ty : TTImp) -> Type where
  TrustMeHT : HasType nm ty

export
hasType : Elaboration m => (nm : Name) ->
          m (Maybe (ty : TTImp ** HasType nm ty))
hasType nm = catch $ do
  [(_, ty)] <- getType nm
    | _ => fail "Ambiguous name"
  pure (ty ** TrustMeHT)

||| Type of proofs that a type is inhabited
export
data IsProvable : (ty : TTImp) -> Type where
  TrustMeIP : IsProvable ty

export
isProvable : Elaboration m => (ty : TTImp) ->
             m (Maybe (IsProvable ty))
isProvable ty = catch $ do
  ty <- check {expected = Type} ty
  ignore $ check {expected = ty} `(%search)
  pure TrustMeIP

||| Type of proofs that a type satisfies a constraint.
||| Internally it's vacuous. We don't export the constructor so
||| that users cannot manufacture buggy proofs.
export
data HasImplementation : (intf : a -> Type) -> TTImp -> Type where
  TrustMeHI : HasImplementation intf t

||| We may need to manufacture proofs and so we provide the `assert` escape hatch.
export %unsafe
assert_hasImplementation : HasImplementation intf t
assert_hasImplementation = TrustMeHI

||| Given
||| @ intf an interface (e.g. `Functor`, or `Bifunctor`)
||| @ t    a term corresponding to a (possibly partially applied) type constructor
||| check whether Idris2 can find a proof that t satisfies the interface.
export
hasImplementation : Elaboration m => (intf : a -> Type) -> (t : TTImp) ->
                    m (Maybe (HasImplementation intf t))
hasImplementation c t = do
  Just prf <- catch $ isFamily t
    | _ => Nothing <$ logMsg "derive.common.hasImplementation" 100
                         "\{show t} is not a Type"
  Just intf <- catch $ quote c
    | _ => Nothing <$ logMsg "derive.common.hasImplementation" 100
                         "Could not quote constraint"
  Just ty <- catch $ check {expected = Type} $
               withParams emptyFC (const Nothing) prf.parameterNames `(~(intf) ~(t))
    | _ => Nothing <$ logMsg "derive.common.hasImplementation" 100
                         "\{show (`(~(intf) ~(t)))} is not a Type"

  Just _ <- catch $ check {expected = ty} `(%search)
    | _ => Nothing <$ logMsg "derive.common.hasImplementation" 100
                         "Could not find an implementation of \{show (`(~(intf) ~(t)))}"
  pure (Just TrustMeHI)

------------------------------------------------------------------------------
-- Utils

||| Optionally eta-expand if there is no argument available
export
optionallyEta : FC -> Maybe TTImp -> (TTImp -> TTImp) -> TTImp
optionallyEta fc (Just t) f = f t
optionallyEta fc Nothing f =
  let tnm = UN $ Basic "t" in
  ILam fc MW ExplicitArg (Just tnm) (Implicit fc False) $
  f (IVar fc tnm)

||| We often apply multiple arguments, this makes things simpler
export
apply : FC -> TTImp -> List TTImp -> TTImp
apply fc t ts = apply t (map (Arg fc) ts)

||| Use unqualified names (useful for more compact printing)
export
cleanup : TTImp -> TTImp
cleanup = \case
  IVar fc n => IVar fc (dropNS n)
  t => t

||| Create fresh names
export
freshName : List TypeParameter -> String -> String
freshName ns a = assert_total $ go (basicNames $ concatMap typeParameterNames ns) Nothing where
  typeParameterNames : TypeParameter -> List Name
  typeParameterNames (MkTPLocal a) = [a]
  typeParameterNames (MkTPPrim c) = []
  typeParameterNames (MkTPApp (n, tp)) = assert_total
    $ n :: concatMap (typeParameterNames . unArg) tp
  typeParameterNames MkTPIType = []

  basicNames : List Name -> List String
  basicNames names = mapMaybe (toBasic . dropNS) names where
    toBasic : Name -> Maybe String
    toBasic (UN (Basic str)) = Just str
    toBasic _ = Nothing

  covering
  go : List String -> Maybe Nat -> String
  go names counter =
    let name = a ++ maybe "" show counter in
    if name `elem` names
      then go names (Just $ maybe 0 S counter)
      else name

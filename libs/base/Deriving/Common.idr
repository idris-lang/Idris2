module Deriving.Common

import Data.SnocList
import Language.Reflection

%default total

------------------------------------------------------------------------------
-- Being free of a variable

||| IsFreeOf is parametrised by
||| @ x  the name of the type variable that the functioral action will change
||| @ ty the type that does not contain any mention of x
export
data IsFreeOf : (x : Name) -> (ty : TTImp) -> Type where
  ||| For now we do not bother keeping precise track of the proof that a type
  ||| is free of x
  TrustMeFO : IsFreeOf a x

||| We may need to manufacture proofs and so we provide the `assert` escape hatch.
export
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
record IsType where
  constructor MkIsType
  typeConstructor  : Name
  parameterNames   : List (Argument Name, Nat)
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

export
isType : Elaboration m => TTImp -> m IsType
isType = go Z [] where

  go : Nat -> List (Argument Name, Nat) -> TTImp -> m IsType
  go idx acc (IVar _ n) = MkIsType n (map (map (minus idx . S)) acc) <$> isTypeCon n
  go idx acc (IApp _ t (IVar _ nm)) = case nm of
    -- Unqualified: that's a local variable
    UN (Basic _) => go (S idx) ((Arg emptyFC nm, idx) :: acc) t
    _ => go (S idx) acc t
  go idx acc (INamedApp _ t nm (IVar _ nm')) = case nm' of
    -- Unqualified: that's a local variable
    UN (Basic _) => go (S idx) ((NamedArg emptyFC nm nm', idx) :: acc) t
    _ => go (S idx) acc t
  go idx acc (IAutoApp _ t (IVar _ nm)) = case nm of
    -- Unqualified: that's a local variable
    UN (Basic _) => go (S idx) ((AutoArg emptyFC nm, idx) :: acc) t
    _ => go (S idx) acc t
  go idx acc t = fail "Expected a type constructor, got: \{show t}"

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
withParams : FC -> (Nat -> Maybe TTImp) -> List (Argument Name, Nat) -> TTImp -> TTImp
withParams fc params nms t = go nms where

  addConstraint : Maybe TTImp -> Name -> TTImp -> TTImp
  addConstraint Nothing _ = id
  addConstraint (Just cst) nm =
     let ty = IApp fc cst (IVar fc nm) in
     IPi fc MW AutoImplicit Nothing ty

  go : List (Argument Name, Nat) -> TTImp
  go [] = t
  go ((arg, pos) :: nms)
    = let nm = unArg arg in
      IPi fc M0 ImplicitArg (Just nm) (Implicit fc True)
    $ addConstraint (params pos) nm
    $ go nms

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
export
assert_hasImplementation : HasImplementation intf t
assert_hasImplementation = TrustMeHI

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
  ty <- check {expected = Type} $ withParams emptyFC (const Nothing) prf.parameterNames `(~(intf) ~(t))
  ignore $ check {expected = ty} `(%search)
  pure TrustMeHI

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

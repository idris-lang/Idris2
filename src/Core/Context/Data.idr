-- Computing the parameters

module Core.Context.Data

import Core.Context
import Core.Context.Log
import Core.Normalise

import Data.List
import Data.Maybe

import Libraries.Data.WithDefault

%default covering

-- If a name appears more than once in an argument list, only the first is
-- considered a parameter
dropReps : List (Maybe (Term vars)) -> List (Maybe (Term vars))
dropReps [] = []
dropReps {vars} (Just (Local fc r x p) :: xs)
    = Just (Local fc r x p) :: assert_total (dropReps (map toNothing xs))
  where
    toNothing : Maybe (Term vars) -> Maybe (Term vars)
    toNothing tm@(Just (Local _ _ v' _))
        = if x == v' then Nothing else tm
    toNothing tm = tm
dropReps (x :: xs) = x :: dropReps xs

updateParams : {auto _ : Ref Ctxt Defs} -> {vars : _} ->
               Maybe (List (Maybe (Term vars))) ->
                  -- arguments to the type constructor which could be
                  -- parameters
                  -- Nothing, as an argument, means this argument can't
                  -- be a parameter position
               List (Term vars) ->
                  -- arguments to an application
               Core (List (Maybe (Term vars)))
updateParams Nothing args = dropReps <$> traverse couldBeParam args
  where
    couldBeParam : Term vars -> Core (Maybe (Term vars))
    couldBeParam tm = pure $ case !(etaContract tm) of
      Local fc r v p => Just (Local fc r v p)
      _ => Nothing
updateParams (Just args) args' = pure $ dropReps $ zipWith mergeArg args args'
  where
    mergeArg : Maybe (Term vars) -> Term vars -> Maybe (Term vars)
    mergeArg (Just (Local fc r x p)) (Local _ _ y _)
        = if x == y then Just (Local fc r x p) else Nothing
    mergeArg _ _ = Nothing

getPs : {auto _ : Ref Ctxt Defs} -> {vars : _} ->
        Maybe (List (Maybe (Term vars))) -> Name -> Term vars ->
        Core (Maybe (List (Maybe (Term vars))))
getPs acc tyn (Bind _ x (Pi _ _ _ ty) sc)
      = do scPs <- getPs (map (map (map weaken)) acc) tyn sc
           pure $ map (map (>>= \ tm => shrink tm (Drop Refl))) scPs
getPs acc tyn tm
    = case getFnArgs tm of
           (Ref _ _ n, args) =>
              if n == tyn
                 then Just <$> updateParams acc args
                 else pure acc
           _ => pure acc

toPos : Maybe (List (Maybe a)) -> List Nat
toPos Nothing = []
toPos (Just ns) = justPos 0 ns
  where
    justPos : Nat -> List (Maybe a) -> List Nat
    justPos i [] = []
    justPos i (Just x :: xs) = i :: justPos (1 + i) xs
    justPos i (Nothing :: xs) = justPos (1 + i) xs

getConPs : {auto _ : Ref Ctxt Defs} -> {vars : _} ->
           Maybe (List (Maybe (Term vars))) -> Name -> Term vars ->
           Core (List Nat)
getConPs acc tyn (Bind _ x (Pi _ _ _ ty) sc)
    = do bacc <- getPs acc tyn ty
         getConPs (map (map (map weaken)) bacc) tyn sc
getConPs acc tyn (Bind _ x (Let _ _ v ty) sc)
    = getConPs acc tyn (subst v sc)
getConPs acc tyn tm = toPos <$> getPs acc tyn tm

paramPos : {auto _ : Ref Ctxt Defs} -> Name -> (dcons : List ClosedTerm) ->
           Core (Maybe (List Nat))
paramPos tyn [] = pure Nothing -- no constructor!
paramPos tyn dcons = do
  candidates <- traverse (getConPs Nothing tyn) dcons
  pure $ Just $ intersectAll candidates

export
addData : {auto c : Ref Ctxt Defs} ->
          Scope -> Visibility -> Int -> DataDef -> Core Int
addData vars vis tidx (MkData (MkCon dfc tyn arity tycon) datacons)
    = do defs <- get Ctxt
         tag <- getNextTypeTag
         let allPos = allDet arity
         -- In case there are no constructors, all the positions are parameter positions!
         let paramPositions = fromMaybe allPos !(paramPos (Resolved tidx) (map type datacons))
         log "declare.data.parameters" 20 $
            "Positions of parameters for datatype" ++ show tyn ++
            ": [" ++ showSep ", " (map show paramPositions) ++ "]"
         let tydef = newDef dfc tyn top vars tycon (specified vis)
                            (TCon tag arity
                                  paramPositions
                                  allPos
                                  defaultFlags [] (Just $ map name datacons) Nothing)
         (idx, gam') <- addCtxt tyn tydef (gamma defs)
         gam'' <- addDataConstructors 0 datacons gam'
         put Ctxt ({ gamma := gam'' } defs)
         pure idx
  where
    allDet : Nat -> List Nat
    allDet Z = []
    allDet (S k) = [0..k]

    conVisibility : Visibility -> Visibility
    conVisibility Export = Private
    conVisibility x = x

    addDataConstructors : (tag : Int) -> List Constructor ->
                          Context -> Core Context
    addDataConstructors tag [] gam = pure gam
    addDataConstructors tag (MkCon fc n a ty :: cs) gam
        = do let condef = newDef fc n top vars ty (specified $ conVisibility vis) (DCon tag a Nothing)
             -- Check 'n' is undefined
             Nothing <- lookupCtxtExact n gam
                 | Just gdef => throw (AlreadyDefined fc n)
             (idx, gam') <- addCtxt n condef gam
             addDataConstructors (tag + 1) cs gam'

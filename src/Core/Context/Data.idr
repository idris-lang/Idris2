-- Computing the parameters

module Core.Context.Data

import Core.Context
import Core.Context.Log

import Data.List
import Data.Maybe

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

updateParams : Maybe (List (Maybe (Term vars))) ->
                  -- arguments to the type constructor which could be
                  -- parameters
                  -- Nothing, as an argument, means this argument can't
                  -- be a parameter position
               List (Term vars) ->
                  -- arguments to an application
               List (Maybe (Term vars))
updateParams Nothing args = dropReps $ map couldBeParam args
  where
    couldBeParam : Term vars -> Maybe (Term vars)
    couldBeParam (Local fc r v p) = Just (Local fc r v p)
    couldBeParam _ = Nothing
updateParams (Just args) args' = dropReps $ zipWith mergeArg args args'
  where
    mergeArg : Maybe (Term vars) -> Term vars -> Maybe (Term vars)
    mergeArg (Just (Local fc r x p)) (Local _ _ y _)
        = if x == y then Just (Local fc r x p) else Nothing
    mergeArg _ _ = Nothing

getPs : {vars : _} ->
        Maybe (List (Maybe (Term vars))) -> Name -> Term vars ->
        Maybe (List (Maybe (Term vars)))
getPs acc tyn (Bind _ x (Pi _ _ _ ty) sc)
      = let scPs = getPs (Prelude.map (Prelude.map (Prelude.map weaken)) acc) tyn sc in
            map (map shrink) scPs
  where
    shrink : Maybe (Term (x :: vars)) -> Maybe (Term vars)
    shrink Nothing = Nothing
    shrink (Just tm) = shrinkTerm tm (DropCons SubRefl)
getPs acc tyn tm
    = case getFnArgs tm of
           (Ref _ _ n, args) =>
              if n == tyn
                 then Just (updateParams acc args)
                 else acc
           _ => acc

toPos : Maybe (List (Maybe a)) -> List Nat
toPos Nothing = []
toPos (Just ns) = justPos 0 ns
  where
    justPos : Nat -> List (Maybe a) -> List Nat
    justPos i [] = []
    justPos i (Just x :: xs) = i :: justPos (1 + i) xs
    justPos i (Nothing :: xs) = justPos (1 + i) xs

getConPs : {vars : _} ->
           Maybe (List (Maybe (Term vars))) -> Name -> Term vars -> List Nat
getConPs acc tyn (Bind _ x (Pi _ _ _ ty) sc)
    = let bacc = getPs acc tyn ty in
          getConPs (map (map (map weaken)) bacc) tyn sc
getConPs acc tyn tm = toPos (getPs acc tyn tm)

paramPos : Name -> (dcons : List ClosedTerm) ->
           Maybe (List Nat)
paramPos tyn [] = Nothing -- no constructor!
paramPos tyn dcons = Just $ intersectAll (map (getConPs Nothing tyn) dcons)

export
addData : {auto c : Ref Ctxt Defs} ->
          List Name -> Visibility -> Int -> DataDef -> Core Int
addData vars vis tidx (MkData (MkCon dfc tyn arity tycon) datacons)
    = do defs <- get Ctxt
         tag <- getNextTypeTag
         let allPos = allDet arity
         -- In case there are no constructors, all the positions are parameter positions!
         let paramPositions = fromMaybe allPos (paramPos (Resolved tidx) (map type datacons))
         log "declare.data.parameters" 20 $
            "Positions of parameters for datatype" ++ show tyn ++
            ": [" ++ showSep ", " (map show paramPositions) ++ "]"
         let tydef = newDef dfc tyn top vars tycon vis
                            (TCon tag arity
                                  paramPositions
                                  allPos
                                  defaultFlags [] (map name datacons) Nothing)
         (idx, gam') <- addCtxt tyn tydef (gamma defs)
         gam'' <- addDataConstructors 0 datacons gam'
         put Ctxt (record { gamma = gam'' } defs)
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
        = do let condef = newDef fc n top vars ty (conVisibility vis) (DCon tag a Nothing)
             (idx, gam') <- addCtxt n condef gam
             -- Check 'n' is undefined
             Nothing <- lookupCtxtExact n gam
                 | Just gdef => throw (AlreadyDefined fc n)
             addDataConstructors (tag + 1) cs gam'

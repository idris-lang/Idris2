module Core.Termination.SizeChange

import Core.Context
import Core.Context.Log
import Core.Name

import Libraries.Data.NameMap
import Libraries.Data.SortedMap
import Libraries.Data.SortedSet

%default covering

Arg : Type
Arg = Nat

Change : Type
Change = List (Maybe (Arg, SizeChange))

public export
Path : Type
Path = List (FC, Name)

export
record ArgChange where
  constructor MkArgChange
  change : Change
  path : Path

-- ignore path
Eq ArgChange where
  (==) a1 a2 = a1.change == a2.change

Ord ArgChange where
  compare a1 a2 = compare a1.change a2.change

Show ArgChange where
  show a = show a.change ++ " @" ++ show a.path

-- sc-graphs to be added
export
WorkList : Type
WorkList = SortedSet (Name, Name, ArgChange)

-- transitively-closed (modulo work list) set of sc-graphs
export
SCSet : Type
SCSet = NameMap (NameMap (SortedSet ArgChange))

export
initSCSet : SCSet
initSCSet = empty

lookupMap : Name -> NameMap (NameMap v) -> NameMap v
lookupMap n m = fromMaybe empty (lookup n m)

lookupSet : Ord v => Name -> NameMap (SortedSet v) -> SortedSet v
lookupSet n m = fromMaybe empty (lookup n m)

lookupGraphs : Name -> Name -> SCSet -> SortedSet ArgChange
lookupGraphs f g = lookupSet g . lookupMap f

selectDom : Name -> SCSet -> SCSet
selectDom f s = insert f (lookupMap f s) empty

selectCod : Name -> SCSet -> SCSet
selectCod g s = map (\m => insert g (lookupSet g m) empty) s

foldl : (acc -> Name -> Name -> ArgChange -> acc) -> acc -> SCSet -> acc
foldl f_acc acc
    = foldlNames (\acc, f =>
        foldlNames (\acc, g =>
          foldl (\acc, c => f_acc acc f g c) acc)
          acc)
        acc

insertGraph : Name -> Name -> ArgChange -> SCSet -> SCSet
insertGraph f g ch s
  = let s_f = lookupMap f s in
    let s_fg = lookupSet g s_f in
    insert f (insert g (insert ch s_fg) s_f) s

composeChange : Change -> Change -> Change
composeChange c1 c2
    = map ((=<<) (\(i, r) => updateArg r <$> getArg i c1)) c2
  where
    getArg : forall a . Nat -> List (Maybe a) -> Maybe a
    getArg _ [] = Nothing
    getArg Z (x :: xs) = x
    getArg (S k) (x :: xs) = getArg k xs

    updateArg : SizeChange -> (Arg, SizeChange) -> (Arg, SizeChange)
    updateArg c arg@(_, Unknown) = arg
    updateArg Unknown (i, _) = (i, Unknown)
    updateArg c (i, Same) = (i, c)
    updateArg c arg@(_, Smaller) = arg

composeArgChange : ArgChange -> ArgChange -> ArgChange
composeArgChange a1 a2
    = MkArgChange
        (composeChange a1.change a2.change)
        (a1.path ++ a2.path)

preCompose : Name -> ArgChange ->
             SCSet ->
             WorkList ->
             Name -> Name -> ArgChange ->
             WorkList
preCompose f ch1 s work _ h ch2
   = let ch = composeArgChange ch1 ch2 in
     if contains ch (lookupGraphs f h s) then
       work
     else
       insert (f, h, ch) work

postCompose : Name -> ArgChange ->
              SCSet ->
              WorkList ->
              Name -> Name -> ArgChange ->
              WorkList
postCompose h ch2 s work f _ ch1
   = let ch = composeArgChange ch1 ch2 in
     if contains ch (lookupGraphs f h s) then
       work
     else
       insert (f, h, ch) work

mutual
  addGraph : {auto c : Ref Ctxt Defs} ->
             Name -> Name -> ArgChange ->
             WorkList ->
             SCSet ->
             SCSet
  addGraph f g ch work s_in
      = let s = insertGraph f g ch s_in
            after = selectDom g s
            work_pre = foldl (preCompose f ch s) work after
            before = selectCod f s
            work_post = foldl (postCompose g ch s) work_pre before in
        transitiveClosure work_post s

  export
  transitiveClosure : {auto c : Ref Ctxt Defs} ->
                      WorkList ->
                      SCSet ->
                      SCSet
  transitiveClosure work s
      = case pop work of
             Nothing => s
             Just ((f, g, ch), work) =>
               addGraph f g ch work s

-- find (potential) chain of calls to given function (inclusive)
export
prefixPath : NameMap (FC, Name) -> Name -> Path
prefixPath pred g = go g []
  where
    go : Name -> Path -> Path
    go g path
        = let Just (l, f) = lookup g pred
             | Nothing => path in
          if f == g then -- we've reached the entry point!
            path
          else
            go f ((l, g) :: path)

findLoops : {auto c : Ref Ctxt Defs} -> SCSet -> Core (NameMap (Maybe Path))
findLoops s
    = do let loops = filterEndos (\a => composeChange a.change a.change == a.change) s
         log "totality.termination.calc" 7 $ "Loops: " ++ show loops
         let terms = map (foldMap (\a => checkDesc a.change a.path)) loops
         pure terms
    where
      filterEndos : (ArgChange -> Bool) -> SCSet -> NameMap (List ArgChange)
      filterEndos p = mapWithKey (\f, m => filter p (Data.SortedSet.toList (lookupSet f m)))

      checkDesc : Change -> Path -> Maybe Path
      checkDesc [] p = Just p
      checkDesc (Just (_, Smaller) :: _) p = Nothing
      checkDesc (_ :: xs) p = checkDesc xs p

export
findNonTerminatingLoop : {auto c : Ref Ctxt Defs} -> SCSet -> Core (Maybe (Name, Path))
findNonTerminatingLoop s
    = do loops <- findLoops s
         pure $ findNonTerminating loops
    where
      findNonTerminating : NameMap (Maybe Path) -> Maybe (Name, Path)
      findNonTerminating = foldlNames (\acc, g, m => map (g,) m <+> acc) empty

export
setPrefixTerminating : {auto c : Ref Ctxt Defs} ->
        Path -> Name -> Core ()
setPrefixTerminating [] g = pure ()
setPrefixTerminating (_ :: []) g = pure ()
setPrefixTerminating ((l, f) :: p) g
    = do setTerminating l f (NotTerminating (BadPath p g))
         setPrefixTerminating p g

addFunctions : {auto c : Ref Ctxt Defs} ->
              Defs ->
              List GlobalDef -> -- functions we're adding
              NameMap (FC, Name) -> -- functions we've already seen (and their predecessor)
              WorkList ->
              Core (Either Terminating (WorkList, NameMap (FC, Name)))
addFunctions defs [] pred work
    = pure $ Right (work, pred)
addFunctions defs (d1 :: ds) pred work
    = do log "totality.termination.calc" 8 $ "Adding function: " ++ show d1.fullname
         calls <- foldlC resolveCall [] d1.sizeChange
         let Nothing = find isNonTerminating calls
            | Just (d2, l, _) => do let g = d2.fullname
                                    log "totality.termination.calc" 7 $ "Non-terminating function call: " ++ show g
                                    let init = prefixPath pred d1.fullname ++ [(l, g)]
                                    setPrefixTerminating init g
                                    pure $ Left (NotTerminating (BadPath init g))
         let (ds, pred, work) = foldl addCall (ds, pred, work) (filter isUnchecked calls)
         addFunctions defs ds pred work
  where
    resolveCall : List (GlobalDef, FC, (Name, Name, ArgChange)) ->
                  SCCall ->
                  Core (List (GlobalDef, FC, (Name, Name, ArgChange)))
    resolveCall calls (MkSCCall g ch l)
        = do Just d2 <- lookupCtxtExact g (gamma defs)
                | Nothing => do log "totality.termination.calc" 7 $ "Not found: " ++ show g
                                pure calls
             pure ((d2, l, (d1.fullname, d2.fullname, MkArgChange ch [(l, d2.fullname)])) :: calls)

    addCall : (List GlobalDef, NameMap (FC, Name), WorkList) ->
                  (GlobalDef, FC, (Name, Name, ArgChange)) ->
                  (List GlobalDef, NameMap (FC, Name), WorkList)
    addCall (ds, pred, work_in) (d2, l, c)
        = let work = insert c work_in in
          case lookup d2.fullname pred of
               Just _ =>
                 (ds, pred, work)
               Nothing =>
                 (d2 :: ds, insert d2.fullname (l, d1.fullname) pred, work)

    isNonTerminating : (GlobalDef, _, _) -> Bool
    isNonTerminating (d2, _, _)
        = case d2.totality.isTerminating of
               NotTerminating _ => True
               _ => False

    isUnchecked : (GlobalDef, _, _) -> Bool
    isUnchecked (d2, _, _)
        = case d2.totality.isTerminating of
               Unchecked => True
               _ => False

export
initWork : {auto c : Ref Ctxt Defs} ->
           Defs ->
           GlobalDef -> -- entry
           Core (Either Terminating (WorkList, NameMap (FC, Name)))
initWork defs def = addFunctions defs [def] (insert def.fullname (def.location, def.fullname) empty) empty

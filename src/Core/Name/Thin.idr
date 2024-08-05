module Core.Name.Thin

-- Thinnings

public export
data Thin : List a -> List a -> Type where
  Refl : Thin xs xs
  Drop : Thin xs ys -> Thin xs (y :: ys)
  Keep : Thin xs ys -> Thin (x :: xs) (x :: ys)

export
none : {xs : List a} -> Thin [] xs
none {xs = []} = Refl
none {xs = _ :: _} = Drop none

{- UNUSED: we actually sometimes want Refl vs. Keep!
||| Smart constructor. We should use this to maximise the length
||| of the Refl segment thus getting more short-circuiting behaviours
export
Keep : Thin xs ys -> Thin (x :: xs) (x :: ys)
Keep Refl = Refl
Keep p = Keep p
-}

export
keeps : (args : List a) -> Thin xs ys -> Thin (args ++ xs) (args ++ ys)
keeps [] th = th
keeps (x :: xs) th = Keep (keeps xs th)

||| Compute the thinning getting rid of the listed de Bruijn indices.
-- TODO: is the list of erased arguments guaranteed to be sorted?
-- Should it?
export
removeByIndices :
  (erasedArgs : List Nat) ->
  (args : Scope) ->
  (args' ** Thin args' args)
removeByIndices es = go 0 where

  go : (currentIdx : Nat) -> (args : Scope) ->
    (args' ** Thin args' args)
  go idx SLNil = (SLNil ** Refl)
  go idx (x :%: xs) =
    let (vs ** th) = go (S idx) xs in
    if idx `elem` es
      then (vs ** Drop th)
      else (x :%: vs ** Keep th)


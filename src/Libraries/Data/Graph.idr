module Libraries.Data.Graph

import Libraries.Data.SortedMap
import Libraries.Data.SortedSet

import Data.List1

-- Mechanically transcribed from
-- https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm#The_algorithm_in_pseudocode
private
record TarjanVertex where
  constructor TV
  index   : Int
  lowlink : Int
  inStack : Bool

private
record TarjanState cuid where
  constructor TS
  vertices           : SortedMap cuid TarjanVertex
  stack              : List cuid
  nextIndex          : Int
  components         : List (List1 cuid)
  impossibleHappened : Bool  -- we should get at least some indication of broken assumptions

initial : Ord cuid => TarjanState cuid
initial = TS empty [] 0 [] False

||| Find strongly connected components in the given graph.
|||
||| Input: map from vertex X to all vertices Y such that there is edge X->Y
||| Output: list of strongly connected components, ordered by output degree descending
export
tarjan : Ord cuid => SortedMap cuid (SortedSet cuid) -> List (List1 cuid)
tarjan {cuid} deps = loop initial (SortedMap.keys deps)
  where
    strongConnect : TarjanState cuid -> cuid -> TarjanState cuid
    strongConnect ts v =
        let ts'' = case SortedMap.lookup v deps of
              Nothing => ts'  -- no edges
              Just edgeSet => loop ts' (SortedSet.toList edgeSet)
          in case SortedMap.lookup v ts''.vertices of
              Nothing => { impossibleHappened := True } ts''
              Just vtv =>
                if vtv.index == vtv.lowlink
                  then createComponent ts'' v []
                  else ts''
      where
        createComponent : TarjanState cuid -> cuid -> List cuid -> TarjanState cuid
        createComponent ts v acc =
          case ts.stack of
            [] => { impossibleHappened := True } ts
            w :: ws =>
              let ts' : TarjanState cuid = {
                      vertices $= SortedMap.adjust w { inStack := False },
                      stack := ws
                    } ts
                in if w == v
                  then { components $= ((v ::: acc) ::) } ts'  -- that's it
                  else createComponent ts' v (w :: acc)

        loop : TarjanState cuid -> List cuid -> TarjanState cuid
        loop ts [] = ts
        loop ts (w :: ws) =
          loop (
            case SortedMap.lookup w ts.vertices of
              Nothing => let ts' = strongConnect ts w in
                case SortedMap.lookup w ts'.vertices of
                  Nothing => { impossibleHappened := True } ts'
                  Just wtv => { vertices $= SortedMap.adjust v { lowlink $= min wtv.lowlink } } ts'

              Just wtv => case wtv.inStack of
                False => ts  -- nothing to do
                True => { vertices $= SortedMap.adjust v { lowlink $= min wtv.index } } ts
          ) ws

        ts' : TarjanState cuid
        ts' = {
            vertices  $= SortedMap.insert v (TV ts.nextIndex ts.nextIndex True),
            stack     $= (v ::),
            nextIndex $= (1+)
          } ts

    loop : TarjanState cuid -> List cuid -> List (List1 cuid)
    loop ts [] =
      if ts.impossibleHappened
        then []
        else ts.components
    loop ts (v :: vs) =
      case SortedMap.lookup v ts.vertices of
        Just _ => loop ts vs  -- done, skip
        Nothing => loop (strongConnect ts v) vs

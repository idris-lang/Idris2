||| Tail-call optimization.
|||
||| Here is a lengthy explanation how this works at the
||| moment. Assume the following call graph of functions f1,f2,f3,f4 all
||| calling each other in tail call position:
|||
||| ```
|||       ------------ f2 ---- f4 (result)
|||      /          /     \
||| f1 ---- f1     /       -- f1
|||      \        /
|||       -- f3 --
||| ```
|||
||| Function `tailCallGraph` creates a directed graph of all toplevel
||| function calls (incoming and outgoing) in tail-call position:
|||
||| ```idris
||| MkCallGraph $ fromList [(f1,[f1,f2,f3]),(f2,[f1,f4]),(f3,[f2])]
|||             $ fromList [(f1,[f1,f2]),(f2,[f1,f3]),(f3,[f1]),(f4,[f2])]
||| ```
|||
||| Mutually tail-recursive functions form a strongly connected
||| component in such a call graph: There is a (directed) path from every function
||| to every other function. Kosaraju's algorithm is used to identify
||| these strongly connected components by mapping every function
||| of a strongly connected component to the same representative (called `root`)
||| of its component. In the above case, this would result in a sorted
||| map of the following structure:
|||
|||
||| ```idris
||| fromList [(f1,f1),(f1,f2),(f1,f3),(f4,f4)]
||| ```idris
|||
||| As can be seen, f1,f2, and f3 all point to the same root (f1), while
||| f4 points to a different root.
|||
||| Such a tail-recursive call graph is now converted to an imperative
||| loop as follows: Let `obj0={h:0, a1:...}` be a Javascript object consisting
||| of a tag `h` and an argument `a1`. `h` indicates, whether `obj0.a1`
||| contains the result of the computation (`h = 1`) or describes
||| a continuation indicating the next function to invoke
||| together with the necessary arguments. A single `step`
||| function will take such an object and use `a1` in a switch
||| statement to decide , which function
||| implementation to invoke (f1,f2,f3).
||| The result will be a new object, again indicating in tag `h`, whether
||| we arrived at a result, or we need to continue looping.
|||
||| Here is an example of two mutually tail-recursive functions
||| together with the generated tail-call optimized code.
|||
||| Original version:
|||
||| ```javascript
||| function fun1(args1){
|||   switch (foo) {
|||     case b1 : return fun2(args2)
|||     case b2 : return fun1(args1')
|||     case b3 : return nonTailCallResult1
|||   }
||| }
|||
||| function fun2(args2){
|||   switch (bar) {
|||     case b1 : return fun1(args1)
|||     default : return nonTailCallResult2
|||   }
||| }
||| ```
|||
||| The above gets converted to the following code:
|||
||| ```javascript
||| function $tc1(args1){
|||   switch (foo) {
|||     case b1 : return {h: 1, a1: () => $tc2(args2)}
|||     case b2 : return {h: 1, a1: () => $tc1(args1')}
|||     case b3 : return {h: 0, a1: nonTailCallResult1 }
|||   }
||| }
|||
||| function fun1(args1){
|||   return __tailRec($tc1(args1))
||| }
|||
||| function tc2(args2){
|||   switch (bar) {
|||     case b1 : return {h: 1, a1: () => $tc1(args1)}
|||     case default : return {h: 0, a1: nonTailCallResult2 }
|||   }
||| }
|||
||| function fun2(args2){
|||   return __tailRec(tc2(args2))
||| }
||| ```
module Compiler.ES.TailRec

import Data.Maybe
import Data.List
import Data.List1
import Data.Strings
import Libraries.Data.Graph
import Libraries.Data.SortedSet
import Libraries.Data.List.Extra as L
import Libraries.Data.SortedMap as M
import Core.Name
import Core.CompileExpr
import Core.Context

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

-- indices of a list starting at 1
indices : List a -> List Int
indices = go 1
  where go : Int -> List a -> List Int
        go _ []       = []
        go i (_ :: t) = i :: go (i+1) t

zipWithIndices : List a -> List (Int,a)
zipWithIndices as = zip (indices as) as

--------------------------------------------------------------------------------
--          Tailcall Graph
--------------------------------------------------------------------------------

||| A toplevel function in a group of mutually tail recursive functions.
public export
record TcFunction where
  constructor MkTcFunction
  ||| Function's name
  name  : Name

  ||| Function's index in its tail call group
  ||| This is used to decide on which branch to choose in
  ||| the next iteration
  index : Int

  ||| Argument list
  args  : List Name

  ||| Function's definition
  exp   : NamedCExp

||| A group of mutually tail recursive toplevel functions.
public export
record TcGroup where
  constructor MkTcGroup
  ||| Index of the group. This is used to generate a uniquely
  ||| named tail call optimize toplevel function.
  index     : Int

  ||| Set of mutually recursive functions.
  functions : SortedMap Name TcFunction

-- tail calls made from an expression
tailCalls : NamedCExp -> SortedSet Name
tailCalls (NmLet _ _ _ z) = tailCalls z
tailCalls (NmApp _ (NmRef _ x) _) = singleton x
tailCalls (NmConCase fc sc xs x) =
  concatMap (\(MkNConAlt _ _ _ _ x) => tailCalls x) xs <+>
  concatMap tailCalls x
tailCalls (NmConstCase fc sc xs x) =
  concatMap (\(MkNConstAlt _ x) => tailCalls x) xs <+>
  concatMap tailCalls x
tailCalls _ = empty

-- in case of larger groups (more than one element)
-- the group contains tailcalls by construction. In case
-- of a single function, we need to check that at least one
-- outgoing tailcall goes back to the function itself.
hasTailCalls : SortedMap Name (SortedSet Name) -> List1 Name -> Bool
hasTailCalls g (x ::: Nil) = maybe False (contains x) $ lookup x g
hasTailCalls _ _           = True

toGroup :  SortedMap Name (Name,List Name,NamedCExp)
        -> (Int,List1 Name)
        -> List (Name,TcGroup)
toGroup funMap (groupIndex,functions) =
  let ns    = zipWithIndices $ forget functions
      group = MkTcGroup groupIndex . fromList $ mapMaybe fun ns
   in (,group) <$> forget functions
  where fun : (Int,Name) -> Maybe (Name,TcFunction)
        fun (fx, n) = do
          (_,args,exp) <- lookup n funMap
          pure (n,MkTcFunction n fx args exp)

-- Returns the connected components of the tail call graph
-- Every function name that is part of a tail-call group
-- (a set of mutually tail-recursive functions)
-- points to a mapping from all function names
-- of its tail-call group to their tail-call indices.
tailCallGroups :  List (Name,List Name,NamedCExp)
               -> SortedMap Name TcGroup
tailCallGroups funs =
  let funMap = M.fromList $ map (\t => (fst t,t)) funs
      graph  = map (\(_,_,x) => tailCalls x) funMap
      groups = filter (hasTailCalls graph) $ tarjan graph
   in fromList $ concatMap (toGroup funMap) (zipWithIndices groups)

--------------------------------------------------------------------------------
--          Converting tail call groups to syntax trees
--------------------------------------------------------------------------------

public export
record Function where
  constructor MkFunction
  name : Name
  args : List Name
  body : NamedCExp

tcFunction : Int -> Name
tcFunction = MN "$tcOpt"

tcArgName : Name
tcArgName = MN "$a" 0

tcContinueName : (groupIndex : Int) -> (functionIndex : Int) -> Name
tcContinueName gi fi = MN ("TcContinue" ++ show gi) fi

tcDoneName : (groupIndex : Int) -> Name
tcDoneName gi = MN "TcDone" gi

conAlt : TcGroup -> TcFunction -> NamedConAlt
conAlt (MkTcGroup tcIx funs) (MkTcFunction n ix args exp) =
  let name = tcContinueName tcIx ix
   in MkNConAlt name DATACON (Just ix) args (toTc exp)

   where mutual
     tcDone : NamedCExp -> NamedCExp
     tcDone x = NmCon EmptyFC (tcDoneName tcIx) DATACON (Just 0) [x]

     tcContinue : (index : Int) -> List NamedCExp -> NamedCExp
     tcContinue ix = NmCon EmptyFC (tcContinueName tcIx ix) DATACON (Just ix)

     toTc : NamedCExp -> NamedCExp
     toTc (NmLet fc x y z) = NmLet fc x y $ toTc z
     toTc x@(NmApp _ (NmRef _ n) xs) =
       case lookup n funs of
         Just v  => tcContinue v.index xs
         Nothing => tcDone x
     toTc (NmConCase fc sc a d) = NmConCase fc sc (map con a) (map toTc d)
     toTc (NmConstCase fc sc a d) = NmConstCase fc sc (map const a) (map toTc d)
     toTc x@(NmCrash _ _) = x
     toTc x = tcDone x

     con : NamedConAlt -> NamedConAlt
     con (MkNConAlt x y tag xs z) = MkNConAlt x y tag xs (toTc z)

     const : NamedConstAlt -> NamedConstAlt
     const (MkNConstAlt x y) = MkNConstAlt x (toTc y)

convertTcGroup : (tailRecLoopName : Name) -> TcGroup -> List Function
convertTcGroup loop g@(MkTcGroup gindex fs) =
  let functions = sortBy (comparing index) $ values fs
      branches  = map (conAlt g) functions
      tcArg     = NmLocal EmptyFC tcArgName
      switch    = NmConCase EmptyFC tcArg branches Nothing
   in MkFunction (tcFunction g.index) [tcArgName] switch ::
      map toFun functions

  where toFun : TcFunction -> Function
        toFun (MkTcFunction n ix args x) =
          let exps  = map (NmLocal EmptyFC) args
              tcArg = NmCon EmptyFC (tcContinueName gindex ix) DATACON (Just ix) exps
              tcFun = NmRef EmptyFC $ tcFunction gindex
              body  = NmApp EmptyFC (NmRef EmptyFC loop) [tcFun,tcArg]
           in MkFunction n args body

||| (Mutual) Tail recursion optimizations: Converts all groups of
||| mutually tail recursive functions to an imperative loop.
tailRecOptim :  SortedMap Name TcGroup
             -> (tcLoopName : Name)
             -> List (Name,List Name,NamedCExp)
             -> List Function
tailRecOptim groups loop ts =
  let regular = mapMaybe toFun ts
      tailOpt = concatMap (convertTcGroup loop) $ values groups
   in tailOpt ++ regular

  where toFun : (Name,List Name,NamedCExp) -> Maybe Function
        toFun (n,args,exp) = case lookup n groups of
          Just _  => Nothing
          Nothing => Just $ MkFunction n args exp

export
functions :  (tcLoopName : Name)
          -> List (Name,FC,NamedDef)
          -> List Function
functions loop dfs =
  let ts = mapMaybe def dfs
   in tailRecOptim (tailCallGroups ts) loop ts
   where def : (Name,FC,NamedDef) -> Maybe (Name,List Name,NamedCExp)
         def (n,_,MkNmFun args x) = Just (n,args,x)
         def _                    = Nothing

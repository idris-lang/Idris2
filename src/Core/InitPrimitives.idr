module Core.InitPrimitives

import Compiler.CompileExpr

import Core.Context
import Core.Primitives

import Data.Nat
import Data.Vect
import Libraries.Data.WithDefault

%default covering

mkFn : {done : _} ->
       (i : Int) ->
       (todo : Nat) -> PrimFn (todo + done) ->
       Vect done (Var vars) -> Term vars
mkFn i Z op args
    = PrimOp EmptyFC op (reverse (map mkLoc args))
  where
    mkLoc : Var vars -> Term vars
    mkLoc (MkVar p) = Local EmptyFC Nothing _ p
mkFn i (S k) op args
    = Bind EmptyFC (MN "arg" i)
           (Lam EmptyFC top Explicit (Erased EmptyFC Placeholder))
           (mkFn (i + 1) k
                 (rewrite sym (plusSuccRightSucc k done) in op)
                 (MkVar First :: map later args))

mkPrim : (arity : Nat) -> PrimFn arity -> Term [<]
mkPrim a op = mkFn 0 a (rewrite plusZeroRightNeutral a in op) []

addPrim : {auto c : Ref Ctxt Defs} ->
          Prim -> Core ()
addPrim p
    = do let fndef = mkPrim (arity p) (fn p)
         let primdef = newDef EmptyFC (opName (fn p)) top [<]
                              (type p) (specified Public)
                              (Function (MkPMDefInfo NotHole False False)
                                        fndef fndef Nothing)
         ignore $ addDef (opName (fn p)) primdef
         setFlag EmptyFC (opName (fn p)) Inline
         compileDef (opName (fn p))

export
addPrimitives : {auto c : Ref Ctxt Defs} -> Core ()
addPrimitives
    = traverse_ addPrim allPrimitives

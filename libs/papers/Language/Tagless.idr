||| This module is based on the paper
||| Dependent Tagless Final
||| by Nicoals Biri

module Language.Tagless

import Data.List.Elem
import Data.List.Quantifiers

%default total

export infixr 0 -#
public export
(-#) : Type -> Type -> Type
a -# b = (0 _ : a) -> b

public export
BinaryOp : Type -> Type
BinaryOp a = a -> a -> a

namespace Section3

  interface Base (0 inter : Type -# Type) where
    int : Int -> inter Int
    add : BinaryOp (inter Int)
    mult : BinaryOp (inter Int)
    and : BinaryOp (inter Bool)
    or : BinaryOp (inter Bool)
    eq : Eq a => inter a -> inter a -> inter Bool
    ite : inter Bool -> BinaryOp (inter a)

  interface Read (0 inter : Type -# Type -# Type) where
    read : inter r r
    chain : inter a b -> inter b c -> inter a c

  public export
  Ctx : Type
  Ctx = List (String, Type)

  interface Var (0 inter : Ctx -# Type -# Type) where
    lam : (lbl : String) -> inter ((lbl, a) :: ctx) b -> inter ctx (a -> b)
    app : inter ctx (a -> b) -> inter ctx a -> inter ctx b
    get : (lbl : String) -> Elem (lbl, a) ctx -> inter ctx a

  record EvalBase (0 a : Type) where
    constructor MkBase
    getValueBase : a

  Base EvalBase where
    int = MkBase
    add = MkBase .: (+) `on` getValueBase
    mult = MkBase .: (*) `on` getValueBase
    and (MkBase b) (MkBase c) = MkBase (b && c)
    or (MkBase b) (MkBase c) = MkBase (b || c)
    eq = MkBase .: (==) `on` getValueBase
    ite (MkBase b) (MkBase t) (MkBase f) = MkBase (ifThenElse b t f)

  record EvalRead (0 r : Type) (0 a : Type) where
    constructor MkRead
    getValueRead : r -> a

  runEvalRead : r -> EvalRead r a -> a
  runEvalRead r (MkRead f) = f r

  Read EvalRead where
    read = MkRead id
    chain (MkRead f) (MkRead g) = MkRead (g . f)

  public export
  Env : Ctx -> Type
  Env = All snd

  record EvalVar (0 ctx : Ctx) (0 a : Type) where
    constructor MkEvalVar
    getValueVar : Env ctx -> a

  Var EvalVar where
    lam lbl (MkEvalVar body) = MkEvalVar $ \ env, x => body (x :: env)
    app (MkEvalVar f) (MkEvalVar t) = MkEvalVar $ \ env => f env (t env)
    get lbl prf = MkEvalVar $ indexAll prf

  -- Mixing two languages: Read & Base
  -- We can somewhat save ourselves by adding a constraint
  -- {0 r : Type} -> Base (inter r)
  testBaseRead : {0 inter : Type -# Type -# Type} ->
                 ({0 r : Type} -> Base (inter r)) =>
                 Read inter =>
                 inter Int Int
  testBaseRead = chain (eq read (int 2)) (ite read (int 4) (int 0))

  -- Basically duplicating the (Base EvalBase) work but adding orthogonal
  -- Reader monad cruft. This is annoyingly verbose...
  Base (EvalRead r) where
    int = MkRead . const
    add m n = MkRead $ \ r => ((+) `on` runEvalRead r) m n
    mult m n = MkRead $ \ r => ((*) `on` runEvalRead r) m n
    eq m n = MkRead $ \ r => ((==) `on` runEvalRead r) m n
    or b c = MkRead $ \ r => runEvalRead r b || runEvalRead r c
    and b c = MkRead $ \ r => runEvalRead r b && runEvalRead r c
    ite b t f = MkRead $ \ r => ifThenElse (runEvalRead r b) (runEvalRead r t) (runEvalRead r f)

  -- But it does work.
  runTest : ([0..3] <&> \ r => runEvalRead r Section3.testBaseRead) === [0,0,4,0]
  runTest = Refl

  -- How are you supposed to compose Base, Read, and Var though?
  -- The constraints on the type of inter are incompatible.

namespace Section4

  -- Solution: index Inter by a notion of context and use mtl-style constraints
  -- on the context type to ensure we have access to the required operations
  -- (cf. ReadContext & Read, or VarContext & Var)

  Inter : Type -> Type
  Inter context = context -> Type -> Type

  interface Base (0 context : Type) (0 inter : Inter context)
            | inter where
    using (ctx : context)
      int : Int -> inter ctx Int
      add : BinaryOp (inter ctx Int)
      mult : BinaryOp (inter ctx Int)
      and : BinaryOp (inter ctx Bool)
      or : BinaryOp (inter ctx Bool)
      eq : Eq a => inter ctx a -> inter ctx a -> inter ctx Bool
      ite : inter ctx Bool -> BinaryOp (inter ctx a)

  interface ReadContext context where
    0 getRead : context -> Type
    0 setRead : Type -> context -> context
    0 getSetId : (ctx : context) -> getRead (setRead a ctx) === a

  interface Read (0 context : Type) (0 inter : Inter context)
            (0 r : ReadContext context) | inter where
    using (ctx : context)
      read : inter ctx (getRead ctx)
      chain : inter ctx a -> inter (setRead a ctx) b -> inter ctx b

  interface VarContext context where
    0 getCtx : context -> Ctx
    0 addVar : (String, Type) -> context -> context
    0 getAddCons : (ctx : context) -> getCtx (addVar v ctx) === v :: getCtx ctx

  interface Var context (0 inter : Inter context)
            (0 v : VarContext context) | inter where
    using (ctx : context)
      lam : (lbl : String) -> inter (addVar (lbl, a) ctx) b -> inter ctx (a -> b)
      app : inter ctx (a -> b) -> inter ctx a -> inter ctx b
      get : (lbl : String) -> Elem (lbl, a) (getCtx ctx) -> inter ctx a

  -- If we only want a reader
  ReadContext Type where
    getRead = id
    setRead = const
    getSetId _ = Refl

  -- If we only want a var
  VarContext Ctx where
    getCtx = id
    addVar = (::)
    getAddCons _ = Refl

  -- If we want both a reader and a var
  record RVCtx where
    constructor MkRVCtx
    cellType : Type
    context : Ctx

  ReadContext RVCtx where
    getRead = cellType
    setRead r = { cellType := r }
    getSetId (MkRVCtx r ctx) = Refl

  VarContext RVCtx where
    getCtx = context
    addVar v = { context $= (v ::) }
    getAddCons (MkRVCtx r ctx) = Refl

  record RVEnv (ctx : RVCtx) where
    constructor MkRVEnv
    cellValue : ctx.cellType
    environment : All Builtin.snd ctx.context

  record Eval (ctx : RVCtx) (a : Type) where
    constructor MkEval
    getEvalValue : RVEnv ctx -> a

  runEval : RVEnv ctx -> Eval ctx a -> a
  runEval r (MkEval f) = f r

  Functor (Eval ctx) where
    map f (MkEval k) = MkEval (f . k)

  Applicative (Eval ctx) where
    pure = MkEval . const
    MkEval f <*> MkEval t = MkEval (\ r => f r (t r))

  Section4.Read RVCtx Eval %search where
    read = MkEval cellValue
    chain {ctx = MkRVCtx a ctx} f g = MkEval $ \ r =>
      runEval ({ cellValue := runEval r f } r) g

  Section4.Var RVCtx Eval %search where
    lam {ctx = MkRVCtx a ctx} lbl body
      = MkEval $ \ (MkRVEnv r env), v => runEval (MkRVEnv r (v :: env)) body
    app f t = [| ($) f t |]
    get x pr = MkEval (indexAll pr . environment)

  Section4.Base RVCtx Eval where
    int x = pure x
    add m n = [| m + n |]
    mult m n = [| m * n |]
    eq m n = [| m == n |]
    -- annoying eta expansions because of Lazy annotations
    and b c = [| (\ b, c => b && c) b c |]
    or b c = [| (\ b, c => b || c) b c |]
    ite b t f = [| (\ b, t, f => ifThenElse b t f) b t f |]

  -- why do we need hiding? Shouldn't the interfaces be limited to the
  -- separate namespace?!
  %hide Section3.add
  %hide Section3.lam
  %hide Section3.get
  %hide Section3.read
  %hide Section3.int

  testExpr : {0 inter : RVCtx -> Type -> Type} ->
             Section4.Base RVCtx inter =>
             Section4.Read RVCtx inter %search =>
             Section4.Var RVCtx inter %search =>
             inter (MkRVCtx Int ctx) (Int -> Int)
  testExpr = lam "x" (add (get "x" Here) (add read (int 5)))

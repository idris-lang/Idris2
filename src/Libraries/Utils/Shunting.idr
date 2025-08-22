module Libraries.Utils.Shunting

import Core.Context
import Core.Core
import Core.FC

%default total

-- The shunting yard algorithm turns a list of tokens with operators into
-- a parse tree expressing the precedence and associativity correctly.
-- We assume that brackets, functions etc are dealt with in a higher level
-- parser, so we're only dealing with operators here.

-- Precedences/associativities
public export
data OpPrec
          = AssocL Nat
          | AssocR Nat
          | NonAssoc Nat
          | Prefix Nat

-- Tokens are either operators or already parsed expressions in some
-- higher level language
public export
data Tok : (op, a : Type) ->  Type where
    Op : (expressionLoc : FC) -> (operatorLoc : FC) -> (operatorInfo : op) -> OpPrec -> Tok op a
    Expr : a -> Tok op a

-- The result of shunting is a parse tree with the precedences made explicit
-- in the tree.
-- NOTE: I have been wondering if I can use types to express that the
-- subtrees use lower precedence operators, but my attempts so far have
-- ended up with more complicated types than the function 'higher', below,
-- which is the one that compares precedences. So I've just used simple
-- types instead and will rely on tests. It would be interesting to see if
-- there's a better way though!

public export
data Tree op a = Infix FC FC op (Tree op a) (Tree op a)
               | Pre FC FC op (Tree op a)
               | Leaf a

public export
Bifunctor Tree where
  bimap f g (Infix fc fc1 x y z) = Infix fc fc1 (f x) (bimap f g y) (bimap f g z)
  bimap f g (Pre fc fc1 x y) = Pre fc fc1 (f x) (bimap f g y)
  bimap f g (Leaf x) = Leaf (g x)

export
(Show op, Show a) => Show (Tree op a) where
  show (Infix _ _ op l r) = "(" ++ show op ++ " " ++ show l ++ " " ++ show r ++ ")"
  show (Pre _ _ op l) = "(" ++  show op ++ " " ++ show l ++ ")"
  show (Leaf val) = show val

Show OpPrec where
  show (AssocL p) = "infixl " ++ show p
  show (AssocR p) = "infixr " ++ show p
  show (NonAssoc p) = "infix " ++ show p
  show (Prefix p) = "prefix " ++ show p

export
(Show op, Show a) => Show (Tok op a) where
  show (Op _ _ op p) = show op ++ " " ++ show p
  show (Expr val) = show val

-- Label for the output queue state
data Out : Type where

output : List (Tree op a) -> Tok op a ->
         Core (List (Tree op a))
output [] (Op {}) = throw (InternalError "Invalid input to shunting")
output (x :: stk) (Op loc opFC str (Prefix _)) = pure $ Pre loc opFC str x :: stk
output (x :: y :: stk) (Op loc opFC str _) = pure $ Infix loc opFC str y x :: stk
output stk (Expr a) = pure $ Leaf a :: stk
output _ _ = throw (InternalError "Invalid input to shunting")

emit : {auto o : Ref Out (List (Tree op a))} ->
       Tok op a -> Core ()
emit t
    = do out <- get Out
         put Out !(output out t)

getPrec : OpPrec -> Nat
getPrec (AssocL k) = k
getPrec (AssocR k) = k
getPrec (NonAssoc k) = k
getPrec (Prefix k) = k

isLAssoc : OpPrec -> Bool
isLAssoc (AssocL _) = True
isLAssoc _ = False

-- Return whether the first operator should be applied before the second.
-- Interpolation to show the operator naked, show to print the operator with its location
higher : Interpolation op => (showLoc : Show op) => FC -> op -> OpPrec -> op -> OpPrec -> Core Bool
higher loc opx op opy (Prefix p) = pure False
higher loc opx (NonAssoc x) opy oy
    = if x == getPrec oy
         then throw (GenericMsgSol loc "Operator \{opx} is non-associative" "Possible solutions"
                                       [ "Add brackets around every use of \{opx}"
                                       , "Change the fixity of \{show opx} to `infixl` or `infixr`"])
         else pure (x > getPrec oy)
higher loc opx ox opy (NonAssoc y)
    = if getPrec ox == y
         then throw (GenericMsgSol loc "Operator \{opy} is non-associative" "Possible solutions"
                                       [ "Add brackets around every use of \{opy}"
                                       , "Change the fixity of \{show opy} to `infixl` or `infixr`"])
         else pure (getPrec ox > y)
higher loc opl l opr r
    = pure $ (getPrec l > getPrec r) ||
             ((getPrec l == getPrec r) && isLAssoc l)

processStack : Interpolation op => (showLoc : Show op) => {auto o : Ref Out (List (Tree op a))} ->
               List (FC, FC, op, OpPrec) -> op -> OpPrec ->
               Core (List (FC, FC, op, OpPrec))
processStack [] op prec = pure []
processStack (x@(loc, opFC, opx, sprec) :: xs) opy prec
    = if !(higher loc opx sprec opy prec)
         then do emit (Op loc opFC opx sprec)
                 processStack xs opy prec
         else pure (x :: xs)

shunt : Interpolation op => (showLoc : Show op) => {auto o : Ref Out (List (Tree op a))} ->
        (opstk : List (FC, FC, op, OpPrec)) ->
        List (Tok op a) -> Core (Tree op a)
shunt stk (Expr x :: rest)
    = do emit (Expr x)
         shunt stk rest
shunt stk (Op loc opFC op prec :: rest)
    = do stk' <- processStack stk op prec
         shunt ((loc, opFC, op, prec) :: stk') rest
shunt stk []
    = do traverse_ (emit . mkOp) stk
         [out] <- get Out
             | out => throw (InternalError "Invalid input to shunting")
         pure out
  where
    mkOp : (FC, FC, op, OpPrec) -> Tok op a
    mkOp (loc, opFC, op, prec) = Op loc opFC op prec

export
parseOps : Interpolation op => (showLoc : Show op) => List (Tok op a) -> Core (Tree op a)
parseOps toks
    = do o <- newRef {t = List (Tree op a)} Out []
         shunt [] toks

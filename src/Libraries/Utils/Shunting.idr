module Libraries.Utils.Shunting

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
data Tok op a = Op FC op OpPrec
              | Expr a

-- The result of shunting is a parse tree with the precedences made explicit
-- in the tree.
-- NOTE: I have been wondering if I can use types to express that the
-- subtrees use lower precedence operators, but my attempts so far have
-- ended up with more complicated types than the function 'higher', below,
-- which is the one that compares precedences. So I've just used simple
-- types instead and will rely on tests. It would be interesting to see if
-- there's a better way though!

public export
data Tree op a = Infix FC op (Tree op a) (Tree op a)
               | Pre FC op (Tree op a)
               | Leaf a

export
(Show op, Show a) => Show (Tree op a) where
  show (Infix _ op l r) = "(" ++ show op ++ " " ++ show l ++ " " ++ show r ++ ")"
  show (Pre _ op l) = "(" ++  show op ++ " " ++ show l ++ ")"
  show (Leaf val) = show val

Show OpPrec where
  show (AssocL p) = "infixl " ++ show p
  show (AssocR p) = "infixr " ++ show p
  show (NonAssoc p) = "infix " ++ show p
  show (Prefix p) = "prefix " ++ show p

export
(Show op, Show a) => Show (Tok op a) where
  show (Op _ op p) = show op ++ " " ++ show p
  show (Expr val) = show val

-- Label for the output queue state
data Out : Type where

output : List (Tree op a) -> Tok op a ->
         Core (List (Tree op a))
output [] (Op _ _ _) = throw (InternalError "Invalid input to shunting")
output (x :: stk) (Op loc str (Prefix _)) = pure $ Pre loc str x :: stk
output (x :: y :: stk) (Op loc str _) = pure $ Infix loc str y x :: stk
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

-- Return whether the first operator should be applied before the second,
-- assuming
higher : Show op => FC -> op -> OpPrec -> op -> OpPrec -> Core Bool
higher loc opx op opy (Prefix p) = pure False
higher loc opx (NonAssoc x) opy oy
    = if x == getPrec oy
         then throw (GenericMsg loc ("Operator '" ++ show opx ++
                                     "' is non-associative"))
         else pure (x > getPrec oy)
higher loc opx ox opy (NonAssoc y)
    = if getPrec ox == y
         then throw (GenericMsg loc ("Operator '" ++ show opy ++
                                     "' is non-associative"))
         else pure (getPrec ox > y)
higher loc opl l opr r
    = pure $ (getPrec l > getPrec r) ||
             ((getPrec l == getPrec r) && isLAssoc l)

processStack : Show op => {auto o : Ref Out (List (Tree op a))} ->
               List (FC, op, OpPrec) -> op -> OpPrec ->
               Core (List (FC, op, OpPrec))
processStack [] op prec = pure []
processStack ((loc, opx, sprec) :: xs) opy prec
    = if !(higher loc opx sprec opy prec)
         then do emit (Op loc opx sprec)
                 processStack xs opy prec
         else pure ((loc, opx, sprec) :: xs)

shunt : Show op => {auto o : Ref Out (List (Tree op a))} ->
        (opstk : List (FC, op, OpPrec)) ->
        List (Tok op a) -> Core (Tree op a)
shunt stk (Expr x :: rest)
    = do emit (Expr x)
         shunt stk rest
shunt stk (Op loc op prec :: rest)
    = do stk' <- processStack stk op prec
         shunt ((loc, op, prec) :: stk') rest
shunt stk []
    = do traverse_ (\s => emit (Op (sloc s) (sop s) (sprec s))) stk
         [out] <- get Out
             | out => throw (InternalError "Invalid input to shunting")
         pure out
  where
    sloc : (annot, b, c) -> annot
    sloc (x, y, z) = x
    sop : (annot, b, c) -> b
    sop (x, y, z) = y
    sprec : (annot, b, c) -> c
    sprec (x, y, z) = z

export
parseOps : Show op => List (Tok op a) -> Core (Tree op a)
parseOps toks
    = do o <- newRef {t = List (Tree op a)} Out []
         shunt [] toks

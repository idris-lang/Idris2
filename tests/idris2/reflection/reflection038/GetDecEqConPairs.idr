import Language.Reflection

%language ElabReflection

data Sum = A | B

data Option a b = Left a | Right b

data TestVect : Nat -> Type -> Type where
    TVNil : TestVect 0 t
    TVCons : t -> TestVect n t -> TestVect (S n) t

data Dir : Type where
	Write : Dir
	Read : Dir

data Expr : (d : Dir) -> Type where
	Lam : (x : String) -> (e : Expr d) -> Expr Write
	Val : (i : Int) -> Expr d
	Proc : (x : String) -> Expr Read

data STree : Nat -> Type -> Type where
  Leaf : STree 0 t
  Node : STree l t -> t -> STree r t -> STree (S (l + r)) t

data Even : Nat -> Type where
  EvenZ  : Even 0
  EvenS : Even n -> Even (S (S n))

data Ty = TInt | TBool | TFunc Ty Ty

data Var : List Ty -> Ty -> Type where
  Here  : Var (t :: ctx) t
  There : Var ctx t -> Var (s :: ctx) t

data Term : List Ty -> Ty -> Type where
  TIntLit : Int -> Term ctx TInt
  TVar : Var ctx t -> Term ctx t
  TLam : Term (a :: ctx) b -> Term ctx (TFunc a b)
  TApp : Term ctx (TFunc a b) -> Term ctx a -> Term ctx b

-- this will not return the expected pairings, which are just the reflexive ones
-- instead it will return all permutations
-- because we can only compare type indices that are variables or (fully applied) constructors
data Compare : Nat -> Nat -> Type where
  CmpLT : (y : Nat) -> Compare x (x + S y)
  CmpEQ : Compare x x
  CmpGT : (x : Nat) -> Compare (y + S x) y

data U = UNat | UBool | UList U

data El : U -> Type where
  ElNat  : Nat -> El UNat
  ElBool  : Bool -> El UBool
  ElList : List (El u) -> El (UList u)

-- this type is nonsensical, but a nice way to see the index / parameter distinction,
-- as well as the compatible and non compatible pairs
data Cursed : Nat -> Type -> Bool -> Type -> Type where
    Cursed1 : Cursed 0 t True u
    Cursed2 : (n : Nat) -> Cursed n t True u
    Cursed3 : (b : Bool) -> Cursed 0 t b u
    Cursed4 : Cursed 0 t False u
    Cursed5 : Cursed n t b u -> Cursed (S n) t b u

tSum : (List Nat, List (String, String))
tSum = %runElab getDecEqConPairs Sum

tOption : (List Nat, List (String, String))
tOption = %runElab getDecEqConPairs Option

tMaybe : (List Nat, List (String, String))
tMaybe = %runElab getDecEqConPairs Maybe

tList : (List Nat, List (String, String))
tList = %runElab getDecEqConPairs List

tVect : (List Nat, List (String, String))
tVect = %runElab getDecEqConPairs TestVect

tExpr : (List Nat, List (String, String))
tExpr = %runElab getDecEqConPairs Expr

tSTree : (List Nat, List (String, String))
tSTree = %runElab getDecEqConPairs STree

tEven : (List Nat, List (String, String))
tEven = %runElab getDecEqConPairs Even

tTerm : (List Nat, List (String, String))
tTerm = %runElab getDecEqConPairs Term

tCompare : (List Nat, List (String, String))
tCompare = %runElab getDecEqConPairs Compare

tEl : (List Nat, List (String, String))
tEl = %runElab getDecEqConPairs El

tCursed : (List Nat, List (String, String))
tCursed = %runElab getDecEqConPairs Cursed

main : IO ()
main = do
    putStrLn (show tSum)
    putStrLn (show tOption)
    putStrLn (show tMaybe)
    putStrLn (show tList)
    putStrLn (show tVect)
    putStrLn (show tExpr)
    putStrLn (show tSTree)
    putStrLn (show tEven)
    putStrLn (show tTerm)
    putStrLn (show tCompare)
    putStrLn (show tEl)
    putStrLn (show tCursed)

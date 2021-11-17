module DerivingEq

import Language.Reflection

%language ElabReflection

public export
countArgs : (ty : TTImp) -> Nat
countArgs (IPi _ _ ExplicitArg _ _ retTy) = 1 + countArgs retTy
countArgs (IPi _ _ _ _ _ retTy) = countArgs retTy
countArgs _ = 0

-- %logging 5
public export
genEq : {t : _} -> Name -> Elab (t -> t -> Bool)
genEq typeName = do
  let pos : FC = MkFC (Virtual Interactive) (0,0) (0,0)
  [(n, _)] <- getType typeName
      | _ => fail "Ambiguous name"
  constrs <- getCons n
  let and : TTImp -> TTImp -> TTImp
      and x y = `(~(x) && ~(y))
      compareEq : String -> String -> TTImp
      compareEq x y = `(~(IVar pos $ UN (Basic x)) == ~(IVar pos $ UN (Basic y)))
      makeClause : Name -> Elab Clause
      makeClause constr = do
        [(_, ty)] <- getType constr
            | _ => fail "ambiguous name for constr"
        let nArgs = countArgs ty
        let xs = map (\i => "x_" ++ show i) $ take nArgs [1..]
        let ys = map (\i => "y_" ++ show i) $ take nArgs [1..]
        let px = foldl (IApp pos) (IVar pos constr) $ map (IBindVar pos) xs
        let py = foldl (IApp pos) (IVar pos constr) $ map (IBindVar pos) ys
        pure $ PatClause pos `(MkPair ~(px) ~(py))
             $ foldl and `(True) $ zipWith compareEq xs ys
      finalClause : Clause
      finalClause = PatClause pos `(_) `(False)
  clauses <- traverse makeClause constrs
  let allClauses = clauses ++ [finalClause]
      caseExpr = ICase pos `(MkPair x y) (Implicit pos True) allClauses
      result = `(\x, y => ~(caseExpr))
  check result
%logging 0

-- This tree works

data TreeOne a = BranchOne (TreeOne a) a (TreeOne a)
               | Leaf

covering
Eq a => Eq (TreeOne a) where
  (==) = %runElab genEq `{ TreeOne }

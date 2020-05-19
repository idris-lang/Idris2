data Name : Type where
  MN : Int -> Name

data IsVar : Name -> List Name -> Type where
  First : IsVar n (n :: ns)
  Later : IsVar n ns -> IsVar n (m :: ns)

data Expr : List Name -> Type where
  CLocal : (prf : IsVar x vars) -> Expr vars

data FunDecl : Type where
  MkFunDecl : (vars : List Name) -> Expr vars -> FunDecl

funDeclWorks : List FunDecl
funDeclWorks = [MkFunDecl [MN 0] (CLocal First)]

foo : Expr [MN 0]
foo = CLocal First

dpairFails : List (vars : List Name ** Expr vars)
dpairFails = [([MN 0] ** CLocal First)]

dpairWithExtraInfoWorks : List (vars : List Name ** Expr vars)
dpairWithExtraInfoWorks = [([MN 0] ** CLocal {x=MN 0} (First {ns=[]}))]

dpairWithExtraInfoBad : List (vars : List Name ** Expr vars)
dpairWithExtraInfoBad = [([MN 0] ** CLocal {x=MN 0} (First {ns=[MN 0]}))]

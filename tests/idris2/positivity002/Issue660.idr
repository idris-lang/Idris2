module Issue660

%default total

%logging "declare.data.parameters" 20

data C : Type -> Type where
  MkC : List a -> C a

data D : Type -> Type where
  MkD : {0 a : Type} -> let 0 b = List a in b -> D a

%logging off

data E : Type where

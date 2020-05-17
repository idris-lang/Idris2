module TTImp.Elab.Prim

import Core.TT

%default covering

export
checkPrim : FC -> Constant -> (Term vars, Term vars)
checkPrim fc (I i) = (PrimVal fc (I i), PrimVal fc IntType)
checkPrim fc (BI i) = (PrimVal fc (BI i), PrimVal fc IntegerType)
checkPrim fc (Str s) = (PrimVal fc (Str s), PrimVal fc StringType)
checkPrim fc (Ch c) = (PrimVal fc (Ch c), PrimVal fc CharType)
checkPrim fc (Db d) = (PrimVal fc (Db d), PrimVal fc DoubleType)
checkPrim fc WorldVal = (PrimVal fc WorldVal, PrimVal fc WorldType)

checkPrim fc IntType = (PrimVal fc IntType, TType fc)
checkPrim fc IntegerType = (PrimVal fc IntegerType, TType fc)
checkPrim fc StringType = (PrimVal fc StringType, TType fc)
checkPrim fc CharType = (PrimVal fc CharType, TType fc)
checkPrim fc DoubleType = (PrimVal fc DoubleType, TType fc)
checkPrim fc WorldType = (PrimVal fc WorldType, TType fc)


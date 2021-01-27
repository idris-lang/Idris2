module TTImp.Elab.Prim

import Core.TT

%default covering

export
checkPrim : FC -> Constant -> (Term vars, Term vars)
checkPrim fc (I i) = (PrimVal fc (I i), PrimVal fc IntType)
checkPrim fc (BI i) = (PrimVal fc (BI i), PrimVal fc IntegerType)
checkPrim fc (B8 i) = (PrimVal fc (B8 i), PrimVal fc Bits8Type)
checkPrim fc (B16 i) = (PrimVal fc (B16 i), PrimVal fc Bits16Type)
checkPrim fc (B32 i) = (PrimVal fc (B32 i), PrimVal fc Bits32Type)
checkPrim fc (B64 i) = (PrimVal fc (B64 i), PrimVal fc Bits64Type)
checkPrim fc (Str s) = (PrimVal fc (Str s), PrimVal fc StringType)
checkPrim fc (Ch c) = (PrimVal fc (Ch c), PrimVal fc CharType)
checkPrim fc (Db d) = (PrimVal fc (Db d), PrimVal fc DoubleType)
checkPrim fc WorldVal = (PrimVal fc WorldVal, PrimVal fc WorldType)

checkPrim fc IntType = (PrimVal fc IntType, TType fc)
checkPrim fc IntegerType = (PrimVal fc IntegerType, TType fc)
checkPrim fc Bits8Type = (PrimVal fc Bits8Type, TType fc)
checkPrim fc Bits16Type = (PrimVal fc Bits16Type, TType fc)
checkPrim fc Bits32Type = (PrimVal fc Bits32Type, TType fc)
checkPrim fc Bits64Type = (PrimVal fc Bits64Type, TType fc)
checkPrim fc StringType = (PrimVal fc StringType, TType fc)
checkPrim fc CharType = (PrimVal fc CharType, TType fc)
checkPrim fc DoubleType = (PrimVal fc DoubleType, TType fc)
checkPrim fc WorldType = (PrimVal fc WorldType, TType fc)

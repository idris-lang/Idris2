module TTImp.Elab.Prim

import Core.TT

%default covering

ttype : FC -> Term vars
ttype fc = TType fc (MN "top" 0)

export
checkPrim : FC -> Constant -> (Term vars, Term vars)
checkPrim fc (I i) = (PrimVal fc (I i), PrimVal fc IntType)
checkPrim fc (I8 i) = (PrimVal fc (I8 i), PrimVal fc Int8Type)
checkPrim fc (I16 i) = (PrimVal fc (I16 i), PrimVal fc Int16Type)
checkPrim fc (I32 i) = (PrimVal fc (I32 i), PrimVal fc Int32Type)
checkPrim fc (I64 i) = (PrimVal fc (I64 i), PrimVal fc Int64Type)
checkPrim fc (BI i) = (PrimVal fc (BI i), PrimVal fc IntegerType)
checkPrim fc (B8 i) = (PrimVal fc (B8 i), PrimVal fc Bits8Type)
checkPrim fc (B16 i) = (PrimVal fc (B16 i), PrimVal fc Bits16Type)
checkPrim fc (B32 i) = (PrimVal fc (B32 i), PrimVal fc Bits32Type)
checkPrim fc (B64 i) = (PrimVal fc (B64 i), PrimVal fc Bits64Type)
checkPrim fc (Str s) = (PrimVal fc (Str s), PrimVal fc StringType)
checkPrim fc (Ch c) = (PrimVal fc (Ch c), PrimVal fc CharType)
checkPrim fc (Db d) = (PrimVal fc (Db d), PrimVal fc DoubleType)
checkPrim fc WorldVal = (PrimVal fc WorldVal, PrimVal fc WorldType)

checkPrim fc IntType = (PrimVal fc IntType, ttype fc)
checkPrim fc Int8Type = (PrimVal fc Int8Type, ttype fc)
checkPrim fc Int16Type = (PrimVal fc Int16Type, ttype fc)
checkPrim fc Int32Type = (PrimVal fc Int32Type, ttype fc)
checkPrim fc Int64Type = (PrimVal fc Int64Type, ttype fc)
checkPrim fc IntegerType = (PrimVal fc IntegerType, ttype fc)
checkPrim fc Bits8Type = (PrimVal fc Bits8Type, ttype fc)
checkPrim fc Bits16Type = (PrimVal fc Bits16Type, ttype fc)
checkPrim fc Bits32Type = (PrimVal fc Bits32Type, ttype fc)
checkPrim fc Bits64Type = (PrimVal fc Bits64Type, ttype fc)
checkPrim fc StringType = (PrimVal fc StringType, ttype fc)
checkPrim fc CharType = (PrimVal fc CharType, ttype fc)
checkPrim fc DoubleType = (PrimVal fc DoubleType, ttype fc)
checkPrim fc WorldType = (PrimVal fc WorldType, ttype fc)

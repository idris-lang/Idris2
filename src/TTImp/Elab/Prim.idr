module TTImp.Elab.Prim

import Core.TT

%default total

export
checkPrim : FC -> Constant -> (Term vars, Term vars)
checkPrim fc (I i)    = (PrimVal fc (I i),    PrimVal fc $ PrT IntType)
checkPrim fc (I8 i)   = (PrimVal fc (I8 i),   PrimVal fc $ PrT Int8Type)
checkPrim fc (I16 i)  = (PrimVal fc (I16 i),  PrimVal fc $ PrT Int16Type)
checkPrim fc (I32 i)  = (PrimVal fc (I32 i),  PrimVal fc $ PrT Int32Type)
checkPrim fc (I64 i)  = (PrimVal fc (I64 i),  PrimVal fc $ PrT Int64Type)
checkPrim fc (BI i)   = (PrimVal fc (BI i),   PrimVal fc $ PrT IntegerType)
checkPrim fc (B8 i)   = (PrimVal fc (B8 i),   PrimVal fc $ PrT Bits8Type)
checkPrim fc (B16 i)  = (PrimVal fc (B16 i),  PrimVal fc $ PrT Bits16Type)
checkPrim fc (B32 i)  = (PrimVal fc (B32 i),  PrimVal fc $ PrT Bits32Type)
checkPrim fc (B64 i)  = (PrimVal fc (B64 i),  PrimVal fc $ PrT Bits64Type)
checkPrim fc (Str s)  = (PrimVal fc (Str s),  PrimVal fc $ PrT StringType)
checkPrim fc (Ch c)   = (PrimVal fc (Ch c),   PrimVal fc $ PrT CharType)
checkPrim fc (Db d)   = (PrimVal fc (Db d),   PrimVal fc $ PrT DoubleType)
checkPrim fc (PrT t)  = (PrimVal fc (PrT t),  TType fc (MN "top" 0))
checkPrim fc WorldVal = (PrimVal fc WorldVal, PrimVal fc $ PrT WorldType)

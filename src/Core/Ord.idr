||| Courtesy of @z-snails
module Core.Ord

import Core.CompileExpr
import Core.Name
import Core.TT
import Data.Vect
import Data.SnocList

import Libraries.Data.Ordering.Extra

lrTag : LazyReason -> Int
lrTag LInf = 0
lrTag LLazy = 1
lrTag LUnknown = 2

export
Ord LazyReason where
    compare l1 l2 = compare (lrTag l1) (lrTag l2)

mutual
    export
    covering
    Eq (CExp vars) where
        CLocal {idx=x1} _ _ == CLocal {idx=x2} _ _ = x1 == x2
        CRef _ n1 == CRef _ n2 = n1 == n2
        CLam _ n1 e1 == CLam _ n2 e2 = case nameEq n1 n2 of
            Just Refl => e1 == e2
            Nothing => False
        CLet _ n1 _ val1 sc1 == CLet _ n2 _ val2 sc2 = case nameEq n1 n2 of
            Just Refl => val1 == val2 && sc1 == sc2
            Nothing => False
        CApp _ f1 a1 == CApp _ f2 a2 = f1 == f2 && a1 == a2
        CCon _ n1 _ t1 a1 == CCon _ n2 _ t2 a2 = t1 == t2 && n1 == n2 && a1 == a2
        COp _ f1 a1 == COp _ f2 a2 = case primFnEq f1 f2 of
            Just Refl => a1 == a2
            Nothing => False
        CExtPrim _ f1 a1 == CExtPrim _ f2 a2 = f1 == f2 && a1 == a2
        CForce _ l1 e1 == CForce _ l2 e2 = l1 == l2 && e1 == e2
        CDelay _ l1 e1 == CDelay _ l2 e2 = l1 == l2 && e1 == e2
        CConCase _ s1 a1 d1 == CConCase _ s2 a2 d2 = s1 == s2 && a1 == a2 && d1 == d2
        CConstCase _ s1 a1 d1 == CConstCase _ s2 a2 d2 = s1 == s2 && a1 == a2 && d1 == d2
        CPrimVal _ c1 == CPrimVal _ c2 = c1 == c2
        CErased _ == CErased _ = True
        CCrash _ m1 == CCrash _ m2 = m1 == m2
        _ == _ = False

    export
    covering
    Eq (CConAlt vars) where
        MkConAlt n1 _ t1 a1 e1 == MkConAlt n2 _ t2 a2 e2 = t1 == t2 && n1 == n2 && case namesEq a1 a2 of
            Just Refl => e1 == e2
            Nothing => False

    export
    covering
    Eq (CConstAlt vars) where
        MkConstAlt c1 e1 == MkConstAlt c2 e2 = c1 == c2 && e1 == e2

mutual
    export
    covering
    Ord (CExp vars) where
        CLocal {idx=x1} _ _ `compare` CLocal {idx=x2} _ _ = x1 `compare` x2
        CRef _ n1 `compare` CRef _ n2 = n1 `compare` n2
        CLam _ n1 e1 `compare` CLam _ n2 e2 = case nameEq n1 n2 of
            Just Refl => compare e1 e2
            Nothing => compare n1 n2
        CLet _ n1 _ val1 sc1 `compare` CLet _ n2 _ val2 sc2 = case nameEq n1 n2 of
            Just Refl => compare val1 val2 `thenCmp` compare sc1 sc2
            Nothing => compare n1 n2
        CApp _ f1 a1 `compare` CApp _ f2 a2 = compare f1 f2 `thenCmp` compare a1 a2
        CCon _ n1 _ t1 a1 `compare` CCon _ n2 _ t2 a2 = compare t1 t2 `thenCmp` compare n1 n2 `thenCmp` compare a1 a2
        COp _ f1 a1 `compare` COp _ f2 a2 = case primFnEq f1 f2 of
            Just Refl => compare a1 a2
            Nothing => primFnCmp f1 f2
        CExtPrim _ f1 a1 `compare` CExtPrim _ f2 a2 = compare f1 f2 `thenCmp` compare a1 a2
        CForce _ l1 e1 `compare` CForce _ l2 e2 = compare l1 l2 `thenCmp` compare e1 e2
        CDelay _ l1 e1 `compare` CDelay _ l2 e2 = compare l1 l2 `thenCmp` compare e1 e2
        CConCase _ s1 a1 d1 `compare` CConCase _ s2 a2 d2 = compare s1 s2 `thenCmp` compare a1 a2 `thenCmp` compare d1 d2
        CConstCase _ s1 a1 d1 `compare` CConstCase _ s2 a2 d2 = compare s1 s2 `thenCmp` compare a1 a2 `thenCmp` compare d1 d2
        CPrimVal _ c1 `compare` CPrimVal _ c2 = compare c1 c2
        CErased _ `compare` CErased _ = EQ
        CCrash _ m1 `compare` CCrash _ m2 = compare m1 m2
        e1 `compare` e2 = compare (tag e1) (tag e2)
          where
            tag : forall vars . CExp vars -> Int
            tag (CLocal _ _) = 0
            tag (CRef _ _) = 1
            tag (CLam _ _ _) = 2
            tag (CLet _ _ _ _ _) = 3
            tag (CApp _ _ _) = 4
            tag (CCon _ _ _ _ _) = 5
            tag (COp _ _ _) = 6
            tag (CExtPrim _ _ _) = 7
            tag (CForce _ _ _) = 8
            tag (CDelay _ _ _) = 9
            tag (CConCase _ _ _ _) = 10
            tag (CConstCase _ _ _ _) = 11
            tag (CPrimVal _ _) = 12
            tag (CErased _) = 13
            tag (CCrash _ _) = 14

    export
    covering
    Ord (CConAlt vars) where
        MkConAlt n1 _ t1 a1 e1 `compare` MkConAlt n2 _ t2 a2 e2 =
            compare t1 t2 `thenCmp` compare n1 n2 `thenCmp` case namesEq a1 a2 of
                Just Refl => compare e1 e2
                Nothing => compare a1 a2

    export
    covering
    Ord (CConstAlt vars) where
        MkConstAlt c1 e1 `compare` MkConstAlt c2 e2 = compare c1 c2 `thenCmp` compare e1 e2

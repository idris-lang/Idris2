module Idris.Desugar.Mutual

import Idris.Syntax

%default total

-- Get the declaration to process on each pass of a mutual block
-- Essentially: types on the first pass
--  i.e. type constructors of data declarations
--       function types
--       interfaces (in full, since it includes function types)
--       records (just the generated type constructor)
--       implementation headers (i.e. note their existence, but not the bodies)
-- Everything else on the second pass
getDecl : Pass -> PDecl -> Maybe PDecl
getDecl p (PImplementation fc vis opts _ is cons n ps iname nusing ds)
    = Just (PImplementation fc vis opts p is cons n ps iname nusing ds)

getDecl p (PNamespace fc ns ds)
    = Just (PNamespace fc ns (assert_total $ mapMaybe (getDecl p) ds))

getDecl AsType d@(PClaim _ _ _ _ _) = Just d
getDecl AsType (PData fc doc vis mbtot (MkPData dfc tyn (Just tyc) _ _))
    = Just (PData fc doc vis mbtot (MkPLater dfc tyn tyc))
getDecl AsType d@(PInterface _ _ _ _ _ _ _ _ _) = Just d
getDecl AsType (PRecord fc doc vis mbtot (MkPRecord n ps _ _ _))
    = Just (PData fc doc vis mbtot (MkPLater fc n (mkRecType ps)))
  where
    mkRecType : List (Name, RigCount, PiInfo PTerm, PTerm) -> PTerm
    mkRecType [] = PType fc
    mkRecType ((n, c, p, t) :: ts) = PPi fc c p (Just n) t (mkRecType ts)
getDecl AsType d@(PFixity _ _ _ _) = Just d
getDecl AsType d@(PDirective _ _) = Just d
getDecl AsType d = Nothing

getDecl AsDef (PClaim _ _ _ _ _) = Nothing
getDecl AsDef d@(PData _ _ _ _ (MkPLater _ _ _)) = Just d
getDecl AsDef (PInterface _ _ _ _ _ _ _ _ _) = Nothing
getDecl AsDef d@(PRecord _ _ _ _ (MkPRecordLater _ _)) = Just d
getDecl AsDef (PFixity _ _ _ _) = Nothing
getDecl AsDef (PDirective _ _) = Nothing
getDecl AsDef d = Just d

getDecl p (PParameters fc ps pds)
    = Just (PParameters fc ps (assert_total $ mapMaybe (getDecl p) pds))
getDecl p (PUsing fc ps pds)
    = Just (PUsing fc ps (assert_total $ mapMaybe (getDecl p) pds))

getDecl Single d = Just d

export
splitMutual : List PDecl -> (List PDecl, List PDecl)
splitMutual ds = (mapMaybe (getDecl AsType) ds, mapMaybe (getDecl AsDef) ds)
